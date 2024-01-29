use core::slice;
use std::io::{self, BufRead, Read};
use std::ops::Range;
use std::sync::atomic::{fence, Ordering};
use std::thread;
use std::time::Duration;

use crate::{IovaRange, Irq, LitePcie};

use super::DmaHalfRegisters;

/// A ring buffer for receiving data from the SoC.
#[derive(Debug)]
pub struct DmaRx<'a> {
    regs: DmaHalfRegisters<'a>,
    /// An interrupt the SoC fires whenever it finishes processing a descriptor
    /// for which `irq_disable` is 0.
    irq: Irq<'a>,

    buf: IovaRange<'a>,

    /// What `DmaTableRegisters::loop_status` was last time we checked. Note
    /// that we always use prog mode, so this is the number of descriptors the
    /// DMA reader's processed since reset.
    last_loop_status: u32,
    /// The number of bytes of `buf` that each descriptor covers.
    descriptor_size: usize,

    /// The start of the range in `buf` that's been filled up by the FPGA and
    /// the user hasn't consumed yet (inclusive).
    filled_start: usize,
    /// The end of the range in `buf` that's been filled up by the FPGA and the
    /// user hasn't consumed yet (exclusive).
    ///
    /// Note that this and `filled_start` aren't a normal range because
    /// `filled_end` is allowed to be less than `filled_start`, when the free
    /// area wraps around the end of `buf`.
    ///
    /// In the scenario where `filled_start == filled_end`, that's interpreted
    /// as a full range; to get an empty range, set `is_empty` to true.
    filled_end: usize,
    /// Whether `buf` currently contains no data from the FPGA.
    is_empty: bool,
}

impl<'a> DmaRx<'a> {
    /// Creates a new `RxBuffer` split up into `num_descriptors` descriptors
    /// that are each `descriptor_size` bytes long.
    pub(crate) fn new(
        litepcie: &'a LitePcie<'a>,
        module: &str,
        regs: DmaHalfRegisters<'a>,
        descriptor_size: usize,
        num_descriptors: usize,
    ) -> crate::Result<Self> {
        assert_eq!(
            descriptor_size % 4,
            0,
            "LitePCIe only supports sending/receiving chunks of data whose sizes are multiples of \
             4 bytes"
        );
        assert!(
            descriptor_size < (1 << 24),
            "LitePCIe descriptor sizes must fit in 24 bits"
        );

        // Reset the DMA writer's descriptor table.
        regs.table().reset().write([1])?;
        // Set the table to prog mode.
        regs.table().loop_prog_n().write([0])?;

        let buf_len = descriptor_size * num_descriptors;
        let this = Self {
            regs,

            // Note that 'writer' here means the one in the SoC, which is writing the stuff we're
            // reading.
            irq: litepcie.irq(&format!("{module}_writer"))?,
            // TODO: throw an error if this goes over 32 bits and the DMA is using 32-bit addresses.
            buf: litepcie.alloc_iova_range(buf_len)?,
            // We reset the descriptor tables on startup, and so the initial `loop_status` should
            // always be 0.
            last_loop_status: 0,
            descriptor_size,
            filled_start: 0,
            filled_end: 0,
            is_empty: true,
        };

        // Give the DMA writer all its initial descriptors.
        for start in (0..this.buf.len()).step_by(descriptor_size) {
            this.add_descriptor(start..start + descriptor_size, true)?;
        }

        // Enable interrupts when a descriptor's completed.
        this.irq.enable()?;
        // Enable the writer.
        regs.enable().write([1])?;

        Ok(this)
    }

    /// Updates the buffer with the knowledge of more filled space.
    fn update(&mut self) -> io::Result<()> {
        let [loop_status] = self.regs.table().loop_status().read()?;
        let descriptors_processed = loop_status.wrapping_sub(self.last_loop_status);
        let descriptors_processed: usize = descriptors_processed.try_into().unwrap();
        self.last_loop_status = loop_status;

        let old_filled_len = self.filled_len();

        self.filled_end += descriptors_processed * self.descriptor_size;
        while self.filled_end >= self.buf.len() {
            self.filled_end -= self.buf.len();
        }

        if descriptors_processed != 0 {
            self.is_empty = false;
        }

        debug_assert_eq!(
            self.filled_len(),
            old_filled_len + descriptors_processed * self.descriptor_size
        );

        Ok(())
    }

    /// Returns the first contiguous piece of this buffer's filled space.
    fn filled(&self) -> Range<usize> {
        if self.filled_start == self.filled_end && !self.is_empty {
            // The whole buffer is full, but we need to make sure that `self.filled_start`
            // is the first byte to be yielded so start from there.
            self.filled_start..self.buf.len()
        } else if self.filled_start <= self.filled_end {
            // The filled area is contiguous.
            self.filled_start..self.filled_end
        } else {
            // The filled area wraps around the end of `buf`, return the first piece of it.
            self.filled_start..self.buf.len()
        }
    }

    fn filled_len(&self) -> usize {
        let mut filled_end = self.filled_end;
        if filled_end < self.filled_start || filled_end == self.filled_start && !self.is_empty {
            filled_end += self.buf.len();
        }
        filled_end - self.filled_start
    }

    /// Add a descriptor to the writer on the FPGA's table, telling it to write
    /// to the given range of bytes (in `self.buf`) and optionally send an
    /// interrupt when it's done.
    fn add_descriptor(&self, range: Range<usize>, irq: bool) -> io::Result<()> {
        let address = self.buf.iova_range().start + range.start as u64;
        let length = range.end - range.start;
        self.regs.table().value().write([
            length as u32
                // Set `irq_disable = !irq`.
                | (!irq as u32) << 24
                // Set `last_disable = 1`.
                | 1 << 25,
            address as u32,
        ])?;
        self.regs.table().we().write([(address >> 32) as u32])
    }
}

impl<'a> BufRead for DmaRx<'a> {
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        // Make sure to do this before `update` so we catch any interrupts fired between
        // then and `wait`.
        if self.filled().is_empty() {
            self.update()?;
            while self.filled().is_empty() {
                // TODO: I couldn't get interrupts to work, so for now we just busy-wait.
                // self.irq.wait()?;
                self.update()?;
            }
        }
        // Make sure we can see the data the FPGA wrote.
        // (I'm not 100% sure if this is actually necessary.)
        fence(Ordering::Acquire);
        let buf_uninit = unsafe { self.buf.slice(self.filled()) };
        Ok(unsafe { slice::from_raw_parts(buf_uninit.as_ptr() as *const u8, buf_uninit.len()) })
    }

    fn consume(&mut self, amt: usize) {
        assert!(amt <= self.filled().len());
        let mut old_filled_start = self.filled_start;
        self.filled_start += amt;

        while old_filled_start / self.descriptor_size != self.filled_start / self.descriptor_size {
            // This has caused a new `descriptor_size`-bytes-long chunk of
            // `self.buf` to become available for the FPGA to write to again;
            // tell it as much.
            self.add_descriptor(
                old_filled_start..old_filled_start + self.descriptor_size,
                true,
            )
            // `consume` can't fail, so we don't have any other option than to panic.
            //
            // The only case where this can fail is if BAR 0 is smaller than it should be though, so
            // it's not likely to come up in regular operation anyway.
            //
            // TODO: maybe check that BAR 0 is big enough up front so we definitely can't panic
            // here.
            .expect("adding descriptor failed");
            old_filled_start += self.descriptor_size;
        }

        if self.filled_start == self.buf.len() {
            self.filled_start = 0;
        }

        if amt != 0 && self.filled_start == self.filled_end {
            // The amount of free space has just been shrunk to 0, so we need to set
            // `is_empty` in order to prevent `filled_start == filled_end` from being
            // interpreted as a full buffer.
            self.is_empty = true;
        }
    }
}

impl<'a> Read for DmaRx<'a> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let src_buf = self.fill_buf()?;
        let copy_len = usize::min(src_buf.len(), buf.len());
        buf[..copy_len].copy_from_slice(&src_buf[..copy_len]);
        let old_filled_len = self.filled_len();
        self.consume(copy_len);
        debug_assert_eq!(self.filled_len(), old_filled_len - copy_len);
        Ok(copy_len)
    }
}

impl Drop for DmaRx<'_> {
    fn drop(&mut self) {
        self.irq.disable().unwrap();
        self.regs.table().reset().write([1]).unwrap();
        thread::sleep(Duration::from_millis(1));
        self.regs.enable().write([0]).unwrap();
        self.regs.table().reset().write([1]).unwrap();
    }
}

// TODO: add destructor.
