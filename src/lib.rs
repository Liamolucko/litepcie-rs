use std::alloc::{handle_alloc_error, Layout};
use std::borrow::Cow;
use std::mem::{ManuallyDrop, MaybeUninit};
use std::ops::Range;
use std::os::fd::{AsFd, AsRawFd, BorrowedFd, OwnedFd};
use std::pin::pin;
use std::ptr::NonNull;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Mutex;
use std::time::Duration;
use std::{io, slice, thread};

use csr::{CsrGroup, CsrRo, CsrRw};
use event_listener::{Event, EventListener};
use pci_driver::device::PciDevice;
use pci_driver::regions::{MappedOwningPciRegion, Permissions};
use rangemap::RangeSet;
use rustix::event::{eventfd, EventfdFlags};
use rustix::io::{ioctl_fionbio, read};

mod soc_info;
pub use soc_info::*;

pub mod csr;
pub mod dma;

pub use pci_driver;
#[doc(hidden)]
pub use std;

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("{0}")]
    Csr(#[from] csr::Error),
    #[error("{0}")]
    Io(#[from] io::Error),
    #[error("PCI device did not have a BAR 0, which is where CSRs are accessed")]
    MissingCsrRegion,
    #[error("no module named {module} in SocInfo")]
    MissingModule { module: String },
    // TODO: replace these with more general errors about constants then add `int_constant`,
    // `string_constant`, `null_constant` methods to `LitePcie`.
    #[error("SoC does not have an interrupt named {name}")]
    NoSuchInterrupt { name: String },
    #[error("interrupt {name}'s index was of type {found}, expected int")]
    InterruptIndexNotInt { name: String, found: &'static str },
    #[error(
        "interrupt {name} has index {index}, when device only has interrupts from 0..{num_irqs}"
    )]
    InterruptIndexOutOfRange {
        name: String,
        index: i32,
        num_irqs: usize,
    },
}

impl From<rustix::io::Errno> for Error {
    fn from(err: rustix::io::Errno) -> Self {
        Self::from(io::Error::from(err))
    }
}

pub type Result<T> = std::result::Result<T, Error>;

/// A handle to an instance of LitePCIe running on a LiteX SoC.
///
/// You don't necessarily need this type: it's not very difficult to access CSRs
/// manually, you just need to call [`CsrGroup::backed_by`] with BAR 0 of the
/// PCI device. However, it's needed for anything where the SoC accesses the
/// host's memory, since it's in charge of keeping track of what regions of IOVA
/// (I/O virtual address) space are used up. It's also needed for dealing with
/// interrupts.
///
/// [`CsrGroup::backed_by`]: csr::CsrGroup::backed_by
#[derive(Debug)]
pub struct LitePcie<'a> {
    /// The `SocInfo` of the SoC this LitePCIe instance is running on, as passed
    /// to [`LitePcie::new`].
    pub soc_info: &'a SocInfo<'a>,
    /// The name of the LitePCIe instance (usually `pcie`).
    pub name: &'a str,
    /// A handle to the PCI device the LitePCIe instance is running on.
    device: &'a dyn PciDevice,
    /// The memory region containing all the SoC's CSRs (BAR 0).
    csr_region: MappedOwningPciRegion,
    /// All the ranges of IOVAs that are currently free for use, in sorted
    /// order.
    ///
    /// Initially this is just `Iommu::valid_iova_ranges`.
    ///
    /// This needs a `Mutex` because there need to be able to be multiple
    /// `IovaRange`s with immutable references to this that mutate it to mark
    /// their ranges as free again on drop.
    free_iovas: Mutex<RangeSet<u64>>,
    /// A lock controlling the access of [`MsiRegisters::enable`] by `Irq`s.
    irq_enable_lock: Mutex<()>,
    /// The state associated with interrupt handling.
    irq_state: IrqState,
}

impl<'a> LitePcie<'a> {
    /// Creates a new handle to a LitePCIe instance on an SoC with the given
    /// info and name (usually just "pcie"), and which is accessible via.
    /// `device`.
    pub fn new(
        soc_info: &'a SocInfo<'a>,
        device: &'a dyn PciDevice,
        name: &'a str,
    ) -> Result<Self> {
        let csr_region = device
            .bar(0)
            .ok_or_else(|| Error::MissingCsrRegion)?
            .map(.., Permissions::ReadWrite)?;

        let iommu = device.iommu();
        let free_iovas = Mutex::new(iommu.valid_iova_ranges().iter().cloned().collect());

        let msi_reg_addrs = MsiRegisters::addrs(soc_info, &format!("{name}_msi"))?;
        let msi_x = msi_reg_addrs.pba.is_some();
        let interrupts = device.interrupts();
        let irq_mechanism = if msi_x {
            interrupts.msi_x()
        } else {
            interrupts.msi()
        };
        let irq_state = if msi_reg_addrs.vector.is_some() && msi_reg_addrs.clear.is_some() {
            IrqState::SingleVector {
                eventfd: eventfd(0, EventfdFlags::empty())?,
                read_lock: AtomicBool::new(false),
                read_event: Event::new(),
            }
        } else {
            IrqState::MultiVector {
                eventfds: (0..irq_mechanism.max())
                    .map(|_| eventfd(0, EventfdFlags::empty()))
                    .collect::<rustix::io::Result<Vec<_>>>()?,
            }
        };
        irq_mechanism.enable(
            &irq_state
                .eventfds()
                .iter()
                .map(|fd| fd.as_raw_fd())
                .collect::<Vec<_>>(),
        )?;

        let this = Self {
            soc_info,
            name,
            device,
            csr_region,
            free_iovas,
            irq_enable_lock: Mutex::new(()),
            irq_state,
        };

        let reset: CsrRw<'_> = this.get_soc_csr_group("ctrl_reset")?;
        reset.write([1])?;
        thread::sleep(Duration::from_millis(10));

        Ok(this)
    }

    /// A helper function to get the CSRs associated with a submodule of this
    /// LitePCIe instance.
    pub fn get_csr_group<'b, T: CsrGroup<'b>>(&'b self, name: &str) -> Result<T> {
        self.get_soc_csr_group(&format!("{}_{}", self.name, name))
    }

    /// A helper function to get any group of CSRs in the SoC, not necessarily
    /// associated with this LitePCIe instance.
    ///
    /// In other words, it doesn't glue `{name}_` onto the start of the CSR's
    /// name like [`Self::get_csr_group`] does.
    pub fn get_soc_csr_group<'b, T: CsrGroup<'b>>(&'b self, name: &str) -> Result<T> {
        let addrs = T::addrs(&self.soc_info, name)?;
        Ok(T::backed_by(&self.csr_region, addrs))
    }

    /// Allocates a new chunk of IOVA (I/O virtual address) space.
    ///
    /// In other words, allocates a buffer that can be read/written to by both
    /// the host and the SoC.
    ///
    /// # Errors
    ///
    /// Forwards any errors in mapping the IOVA space, and returns an
    /// `ErrorKind::OutOfMemory` if there isn't enough free IOVA space left to
    /// map.
    pub fn alloc_iova_range<'b>(&'b self, size: usize) -> io::Result<IovaRange<'b>> {
        if size == 0 {
            return Ok(IovaRange {
                litepcie: self,
                buf: NonNull::dangling(),
                iova_range: 0..0,
            });
        }

        let iommu = self.device.iommu();

        // Pick the free range to allocate a chunk of.
        let mut free_iovas = self.free_iovas.lock().unwrap();
        let free_range = free_iovas
            .iter()
            .find(|range| {
                // If `size` is too big to fit in a `u64`, `range` definitely won't be big
                // enough. (This is impossible until we get 128-bit computers anyway but may as
                // well handle it.)
                u64::try_from(size).map_or(false, |size| {
                    let Ok(alignment) = u64::try_from(iommu.alignment()) else {
                        return false;
                    };
                    range.end - range.start.next_multiple_of(alignment) >= size
                })
            })
            .ok_or(io::Error::new(
                io::ErrorKind::OutOfMemory,
                "not enough free IOVA space",
            ))?;
        let free_range = free_range.clone();

        // We already checked that everything fits into a `u64` while finding
        // `free_range`, so it's fine to just `unwrap` now.
        let iova_start = free_range
            .start
            .next_multiple_of(iommu.alignment().try_into().unwrap());
        let iova_end = iova_start + u64::try_from(size).unwrap();

        // Now allocate the space in RAM we're going to map the IOVA space to.

        // We have to use raw allocation here instead of `Box` or something thanks to
        // the alignment restrictions.
        let layout = Layout::from_size_align(size, iommu.alignment())
            .map_err(|err| io::Error::new(io::ErrorKind::InvalidInput, err))?;
        // SAFETY: We do an early return if `size == 0`, and so we know that `layout`
        // isn't zero-sized.
        let buf = unsafe { std::alloc::alloc(layout) };
        let Some(buf) = NonNull::new(buf) else {
            handle_alloc_error(layout);
        };

        /// A helper struct that frees the contained pointer using the contained
        /// layout on drop.
        struct FreeOnDrop(NonNull<u8>, Layout);

        impl FreeOnDrop {
            fn into_inner(self) -> NonNull<u8> {
                let this = ManuallyDrop::new(self);
                this.0
            }
        }

        impl Drop for FreeOnDrop {
            fn drop(&mut self) {
                unsafe { std::alloc::dealloc(self.0.as_ptr(), self.1) }
            }
        }

        let buf = FreeOnDrop(buf, layout);

        unsafe {
            self.device.iommu().map(
                iova_start,
                size,
                buf.0.as_ptr().cast_const(),
                Permissions::ReadWrite,
            )?
        }

        free_iovas.remove(iova_start..iova_end);

        Ok(IovaRange {
            litepcie: self,
            buf: buf.into_inner(),
            iova_range: iova_start..iova_end,
        })
    }

    /// Returns a handle to the IRQ with the given name.
    pub fn irq<'b>(&'b self, name: &str) -> Result<Irq<'b>> {
        let irq_index = self
            .soc_info
            .constants
            .get(&Cow::Owned(format!("{}_{}_interrupt", self.name, name)))
            .ok_or_else(|| Error::NoSuchInterrupt {
                name: name.to_owned(),
            })?;

        let Some(SocConstant::Integer(irq_index)) = irq_index else {
            return Err(Error::InterruptIndexNotInt {
                name: name.to_owned(),
                found: match irq_index {
                    Some(SocConstant::String(_)) => "string",
                    Some(SocConstant::Integer(_)) => unreachable!(),
                    None => "null",
                },
            });
        };

        let num_irqs = match self.irq_state {
            // There isn't actually any way to tell how many interrupts the SoC's using, but the
            // CSRs have room for 32.
            //
            // TODO: in theory there can be more but we don't support dynamically-sized CSRs yet.
            IrqState::SingleVector { .. } => 32,
            IrqState::MultiVector { ref eventfds } => eventfds.len(),
        };

        let irq_index = usize::try_from(*irq_index)
            .ok()
            .filter(|&index| index < num_irqs)
            .ok_or_else(|| Error::InterruptIndexOutOfRange {
                name: name.to_owned(),
                index: *irq_index,
                num_irqs,
            })?;

        let msi_regs: MsiRegisters = self.get_csr_group("msi")?;
        Ok(match self.irq_state {
            IrqState::SingleVector {
                ref eventfd,
                ref read_lock,
                ref read_event,
            } => Irq {
                index: irq_index,
                enable: msi_regs.enable(),
                enable_lock: &self.irq_enable_lock,
                fd: eventfd.as_fd(),
                single_vector_state: Some(SingleVectorState {
                    // If these didn't exist, `self.irq_state` wouldn't be `SingleVector`.
                    vector: msi_regs.vector().unwrap(),
                    clear: msi_regs.clear().unwrap(),
                    read_lock,
                    read_event,
                }),
            },
            IrqState::MultiVector { ref eventfds } => Irq {
                index: irq_index,
                enable: msi_regs.enable(),
                enable_lock: &self.irq_enable_lock,
                fd: eventfds[irq_index].as_fd(),
                single_vector_state: None,
            },
        })
    }
}

/// A chunk of allocated IOVA space, along with a heap-allocated buffer that
/// it's mapped to.
#[derive(Debug)]
pub struct IovaRange<'a> {
    /// A handle to the IOMMU that this range was mapped with so that we can
    /// unmap it on drop.
    litepcie: &'a LitePcie<'a>,
    /// The start of the buffer that the IOVA space is mapped to.
    buf: NonNull<u8>,
    /// The range of IOVAs that maps to `buf`.
    iova_range: Range<u64>,
}

impl<'a> IovaRange<'a> {
    /// Returns the range of IOVAs this represents.
    pub fn iova_range(&self) -> Range<u64> {
        self.iova_range.clone()
    }

    /// Returns the length of this chunk of IOVA space.
    pub fn len(&self) -> usize {
        (self.iova_range.end - self.iova_range.start)
            .try_into()
            .unwrap()
    }

    /// Returns the given slice of this IOVA range.
    ///
    /// # Panics
    ///
    /// Panics if `range.start > range.end` or `range.end > self.len()`.
    ///
    /// # Safety
    ///
    /// The given range must not be accessed by the SoC while the returned
    /// reference still exists.
    pub unsafe fn slice(&self, range: Range<usize>) -> &[MaybeUninit<u8>] {
        if range.start > range.end {
            panic!("invalid range");
        } else if range.end > self.len() {
            panic!("range out of bounds");
        }
        slice::from_raw_parts(self.buf.as_ptr().add(range.start) as *const _, range.len())
    }

    /// Returns the given mutable slice of this IOVA range.
    ///
    /// # Panics
    ///
    /// Panics if `range.start > range.end` or `range.end > self.len()`.
    ///
    /// # Safety
    ///
    /// The given range must not be accessed by the SoC while the returned
    /// reference still exists.
    pub unsafe fn slice_mut(&mut self, range: Range<usize>) -> &mut [MaybeUninit<u8>] {
        if range.start > range.end {
            panic!("invalid range");
        } else if range.end > self.len() {
            panic!("range out of bounds");
        }
        slice::from_raw_parts_mut(self.buf.as_ptr().add(range.start) as *mut _, range.len())
    }
}

impl<'a> Drop for IovaRange<'a> {
    fn drop(&mut self) {
        if self.iova_range.start == self.iova_range.end {
            // Empty `IovaRange`s don't actually allocate or map anything.
            return;
        }

        // Free/unmap everything.
        self.litepcie
            .device
            .iommu()
            .unmap(self.iova_range.start, self.len())
            .unwrap();
        unsafe {
            std::alloc::dealloc(
                self.buf.as_ptr(),
                Layout::from_size_align(self.len(), self.litepcie.device.iommu().alignment())
                    .unwrap(),
            )
        }

        // Mark this IOVA range as free again.
        let mut free_iovas = self.litepcie.free_iovas.lock().unwrap();
        free_iovas.insert(self.iova_range.clone());
    }
}

unsafe impl Send for IovaRange<'_> {}
unsafe impl Sync for IovaRange<'_> {}

/// The state associated with handling interrupts from the SoC.
#[derive(Debug)]
enum IrqState {
    /// The SoC is using single-vector MSI mode.
    SingleVector {
        /// The `eventfd` which signals any interrupt firing.
        eventfd: OwnedFd,
        /// A lock that controls which task/thread's job it is to read from the
        /// `eventfd`.
        read_lock: AtomicBool,
        /// An event that will be fired after reading from the `eventfd`
        /// succeeds; this is listened to by all the tasks/threads that
        /// failed to acquire `read_lock`.
        read_event: Event,
    },
    /// The SoC is using multi-vector MSI or MSI-X mode.
    MultiVector {
        /// For each interrupt, an `eventfd` that's signalled (has 1 added to
        /// its counter) when the interrupt fires.
        eventfds: Vec<OwnedFd>,
    },
}

impl IrqState {
    /// Returns the list of `eventfd`s that need to be registered in
    /// [`pci_driver::interrupts::PciInterruptMechanism`].
    fn eventfds(&self) -> &[OwnedFd] {
        match self {
            IrqState::SingleVector { eventfd, .. } => slice::from_ref(eventfd),
            IrqState::MultiVector { eventfds } => &eventfds,
        }
    }
}

csr_struct! {
    /// All the CSRs associated with a LitePCIe instance's MSI module.
    ///
    /// The MSI module has 3 modes (technically 3 different modules that get
    /// switched out):
    /// - Single-vector MSI mode, where there's only one physical vector and you use
    ///   `vector`/`clear` to figure out which kind of interrupt it was.
    /// - Multi-vector MSI mode, where each interrupt gets a real vector.
    /// - MSI-X mode, which works the same as multi-vector MSI mode except that
    ///   it's MSI-X.
    struct MsiRegisters<'a> {
        /// A writable bitfield where the nth bit controls whether the nth
        /// interrupt is enabled.
        enable: CsrRw<'a>,
        /// A bitfield where writing a 1 to the nth bit clears that bit in `vector`.
        ///
        /// Only present in single-vector MSI mode.
        clear: Option<CsrRw<'a>>,
        /// A bitfield where the nth bit represents whether the nth interrupt
        /// has fired since it was last cleared via. `clear`.
        ///
        /// Only present in single-vector MSI mode.
        vector: Option<CsrRo<'a>>,
        /// 'MSI-X PBA Table'.
        ///
        /// I have no idea what this actually does; its purpose from this
        /// driver's perspective is just to figure out if we're using MSI-X
        /// interrupts, since this CSR only exists in MSI-X mode.
        pba: Option<CsrRo<'a>>,
    }
}

/// A handle to one of a LitePCIe instance's MSI (or MSI-X) interrupts.
#[derive(Debug)]
pub struct Irq<'a> {
    /// The index of the interrupt.
    index: usize,
    /// A writable CSR containing which interrupts are enabled.
    enable: CsrRw<'a>,
    /// A lock that must be acquired before updating `enable`.
    ///
    /// This can't contain `enable` because it's a field of `LitePcie`, and so
    /// that would make it a self-referential struct.
    enable_lock: &'a Mutex<()>,
    /// The `eventfd` that indicates when an interrupt has occured.
    fd: BorrowedFd<'a>,
    /// When in single-vector MSI mode (the default), the extra state needed to
    /// synchronise with other `Irq`s we're sharing the `eventfd` with and
    /// figure out whether an incoming MSI is intended for this interrupt or
    /// not.
    single_vector_state: Option<SingleVectorState<'a>>,
}

/// All the information / CSRs needed to figure out whether an incoming MSI is a
/// particular interrupt.
#[derive(Debug)]
pub struct SingleVectorState<'a> {
    /// The CSR indicating which interrupts have fired since they were last
    /// cleared.
    vector: CsrRo<'a>,
    /// A CSR for writing which interrupts should be cleared.
    clear: CsrRw<'a>,
    /// An `AtomicBool` controlling which task/thread's job it is to read from
    /// the `eventfd`.
    read_lock: &'a AtomicBool,
    /// An event that will be fired after reading from the `eventfd` succeeds;
    /// this is listened to by all the tasks/threads that failed to acquire
    /// `read_lock`.
    read_event: &'a Event,
}

impl<'a> Irq<'a> {
    /// Enables this interrupt.
    ///
    /// If you don't call this before calling `wait`, it'll block forever.
    pub fn enable(&self) -> io::Result<()> {
        let _guard = self.enable_lock.lock().unwrap();
        let [mut enable] = self.enable.read()?;
        enable |= 1 << self.index;
        self.enable.write([enable])
    }

    /// Diables this interrupt.
    pub fn disable(&self) -> io::Result<()> {
        let _guard = self.enable_lock.lock().unwrap();
        let [mut enable] = self.enable.read()?;
        enable &= !(1 << self.index);
        self.enable.write([enable])
    }

    /// Waits for this interrupt to fire.
    ///
    /// Although this only takes `&self`, you shouldn't `wait` on the same `Irq`
    /// more than once in parallel; some of the `Irq`s might miss the
    /// notification.
    pub fn wait(&self) -> io::Result<()> {
        let mut buf = [0; 8];
        if let Some(state) = &self.single_vector_state {
            let mut listener = pin!(EventListener::new());
            loop {
                // Start listening for events now so that we don't miss any between reading the
                // CSR and actually waiting for them.
                listener.as_mut().listen(&state.read_event);
                let [vector] = state.vector.read()?;
                if vector & (1 << self.index) != 0 {
                    // We've received the interrupt, so now we clear it.
                    state.clear.write([1 << self.index])?;
                    return Ok(());
                }
                if !state.read_lock.swap(true, Ordering::Relaxed) {
                    // The `read_lock` was previously false, meaning we were the first to acquire it
                    // and it's our job to read from the `eventfd`.

                    // Make sure the file is in blocking mode, then read from it.
                    //
                    // Don't propagate errors just yet, otherwise all the tasks/threads waiting on
                    // `read_event` will be stuck there forever.
                    let result =
                        ioctl_fionbio(self.fd, false).and_then(|()| read(self.fd, &mut buf));
                    // `Event` doesn't have a `notify_all` method, but it's impossible to create
                    // `usize::MAX` listeners so this should work fine.
                    state.read_event.notify(usize::MAX);
                    state.read_lock.store(false, Ordering::Relaxed);
                    result?;
                } else {
                    // Someone else is already reading the `eventfd` for us, so just wait for them
                    // to send an event once they're done.
                    listener.as_mut().wait();
                }
            }
        } else {
            read(self.fd, &mut buf)?;
        }
        Ok(())
    }

    /// Waits asynchronously for this interrupt to fire.
    ///
    /// Although this only takes `&self`, you shouldn't `wait` on the same `Irq`
    /// more than once in parallel; some of the `Irq`s might miss the
    /// notification.
    #[cfg(feature = "async")]
    pub async fn wait_async(&self) -> io::Result<()> {
        use async_io::Async;

        let mut buf = [0; 8];
        if let Some(state) = &self.single_vector_state {
            let mut listener = pin!(EventListener::new());
            // Start listening for events now so that we don't miss any between reading the
            // CSR and actually waiting for them.
            listener.as_mut().listen(&state.read_event);
            loop {
                let [vector] = state.vector.read()?;
                if vector & (1 << self.index) != 0 {
                    // We've received the interrupt, so now we clear it.
                    state.clear.write([1 << self.index])?;
                    return Ok(());
                }
                if !state.read_lock.swap(true, Ordering::Relaxed) {
                    // The `read_lock` was previously false, meaning we were the first to acquire it
                    // and it's our job to read from the `eventfd`.
                    //
                    // Don't propagate errors just yet, otherwise all the tasks/threads waiting on
                    // `read_event` will be stuck there forever.
                    let result = Async::new(self.fd);
                    let result = match result {
                        Ok(wrapper) => {
                            wrapper
                                .read_with(|fd| read(fd, &mut buf).map_err(io::Error::from))
                                .await
                        }
                        Err(e) => Err(e),
                    };
                    // `Event` doesn't have a `notify_all` method, but it's impossible to create
                    // `usize::MAX` listeners so this should work fine.
                    state.read_event.notify(usize::MAX);
                    state.read_lock.store(false, Ordering::Relaxed);
                    result?;
                } else {
                    // Someone else is already reading the `eventfd` for us, so just wait for them
                    // to send an event once they're done.
                    listener.as_mut().await;
                }
            }
        } else {
            Async::new(self.fd)?
                .read_with(|fd| read(fd, &mut buf).map_err(io::Error::from))
                .await?;
        }
        Ok(())
    }
}
