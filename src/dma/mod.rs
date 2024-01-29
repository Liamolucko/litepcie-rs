use std::borrow::Cow;
use std::thread;
use std::time::Duration;

use crate::csr::{self, CsrRo, CsrRw};
use crate::{csr_struct, LitePcie};

mod rx;
mod tx;

pub use rx::*;
pub use tx::*;

csr_struct! {
    /// All the CSRs associated with a LitePCIe DMA.
    pub struct DmaRegisters<'a> {
        /// All the CSRs associated with the DMA's write half (the bit that
        /// sends data from the SoC to the host).
        writer: Option<DmaHalfRegisters<'a>>,
        /// All the CSRs associated with the DMA's read half (the bit that
        /// receives data from the host).
        reader: Option<DmaHalfRegisters<'a>>,
        /// All the CSRs associated with the DMA's loopback module.
        loopback: Option<DmaLoopbackRegisters<'a>>,
        /// All the CSRs associated with the DMA's buffering module.
        buffering: Option<DmaBufferingRegisters<'a>>,
    }
}

csr_struct! {
    /// All the CSRs associated with the read/write half of a LitePCIe DMA.
    pub(crate)struct DmaHalfRegisters<'a> {
        /// A bitfield:
        /// - Bit 0: Whether this half of the DMA is enabled (writable).
        /// - Bit 1: Whether this half of the DMA is idle.
        enable: CsrRw<'a>,
        /// All the CSRs associated with this half of the DMA's table of
        /// descriptors.
        table: DmaTableRegisters<'a>,
    }
}

csr_struct! {
    /// All the CSRs associated with a table of LitePCIe DMA descriptors.
    pub(crate)struct DmaTableRegisters<'a> {
        /// The first 64 bits of the descriptor to write to the table, containing:
        /// - Bits 0-23: `length`, the length of the descriptor (in bytes).
        /// - Bit 24: `irq_disable`, determines whether or not an MSI interrupt
        ///   should be sent to the host after this descriptor is executed.
        /// - Bit 25: `last_disable`, 1 = always execute whole descriptor, 0 =
        ///   stop executing early when `last` signal is asserted.
        ///
        ///   This bit only has an effect on the DMA writer (sending data from
        ///   the SoC to the host). When the descriptor gets cut off early, the
        ///   rest of the buffer is just left unwritten to, and so effectively
        ///   creates a gap of random garbage (whatever happened to be in that
        ///   memory before) in the stream from the host's perspective.
        ///
        ///   I'm not entirely sure if that prevents the last bit of sent data
        ///   from not being sent though; the descriptor gets cut off early at
        ///   the level of the max. size of a PCIe transaction, but I'm not sure
        ///   if it also gets cut off early within that PCIe transaction.
        ///
        ///   Regardless, it seems like it'd be tricky to work with weird gaps
        ///   in the stream and so I'm going to leave this as always 1 for the
        ///   time being.
        /// - Bits 26-31: Unused.
        /// - Bits 32-63: The low 32 bits of the address in the CPU's memory to
        ///   read/write from.
        value: CsrRw<'a, 2>,
        /// The final 32 bits of the descriptor to write, which are the high 32
        /// bits of  the address in the CPU's memory to read/write from.
        ///
        /// Writing to this register triggers the whole descriptor to be added
        /// to the table (hence why it's called 'write-enable' instead of just
        /// `value2` or something).
        we: CsrRw<'a>,
        /// Whether the table is in loop mode or prog mode.
        ///
        /// 0 = prog mode, 1 = loop mode.
        loop_prog_n: CsrRw<'a>,
        /// Indicates how many descriptors in the table have been processed.
        ///
        /// In prog mode, this is literally just the number of descriptors that
        /// have been processed since reset.
        ///
        /// In loop mode, the lower 16 bits are the number of descriptors that
        /// have been processed this time through the loop, and the upper 16
        /// bits are the number of iterations through the loop that have occured
        /// since reset.
        loop_status: CsrRo<'a>,
        /// How many descriptors are currently in the table.
        level: CsrRo<'a>,
        /// A CSR which you can write 1 to to reset the table.
        reset: CsrRw<'a>,
    }
}

csr_struct! {
    /// All the CSRs associated with a LiteCPIe DMA's loopback module.
    struct DmaLoopbackRegisters<'a> {
        /// Whether to enable loopback.
        ///
        /// When this is 1, all that the DMA does is send all data it receives
        /// back to the host again.
        enable: CsrRw<'a>,
    }
}

csr_struct! {
    /// All the CSRs associated with a LiteCPIe DMA's buffering module.
    struct DmaBufferingRegisters<'a> {
        reader_fifo: Option<DmaBufferingFifoRegisters<'a>>,
        writer_fifo: Option<DmaBufferingFifoRegisters<'a>>,
    }
}

csr_struct! {
    /// All the CSRs associated with one of a LiteCPIe DMA's buffering module's
    /// FIFOs.
    struct DmaBufferingFifoRegisters<'a> {
        // i'm not using this feature so I can't be bothered to figure out and
        // document what these do.
        control: CsrRw<'a>,
        status: CsrRo<'a>,
    }
}

/// A driver for a LitePCIe DMA.
pub struct Dma<'a> {
    pub tx: Option<DmaTx<'a>>,
    pub rx: Option<DmaRx<'a>>,
}

impl<'a> Dma<'a> {
    /// Makes a new `Dma` from the given PCI subregion (which should be the
    /// SoC's BAR 0), `SocInfo` and the name of the DMA (usually `pcie_dma{n}`).
    pub fn new(
        litepcie: &'a LitePcie<'a>,
        module: &str,
        rx_size: usize,
        loopback: bool,
    ) -> crate::Result<Self> {
        if !litepcie
            .soc_info
            .csr_bases
            .contains_key(&Cow::Owned(format!("{}_{}", litepcie.name, module)))
        {
            // In most cases, you should be able to just rely on a 'missing CSR'
            // error for telling the user if `module` is invalid; however, in
            // the case of DMA, it's technically valid to turn off every single
            // feature of the DMA and for it to have no CSRs. That means that an
            // invalid module name is interpreted as a DMA with all features
            // disabled, hence why we need this extra check.
            return Err(crate::Error::MissingModule {
                module: module.to_owned(),
            });
        }

        let regs: DmaRegisters<'_> = litepcie.get_csr_group(module)?;
        if loopback {
            let Some(loopback) = regs.loopback() else {
                return Err(crate::Error::Csr(csr::Error::MissingCsr {
                    csr: format!("{}_{}_loopback", litepcie.name, module),
                }));
            };
            loopback.enable().write([1])?;
        }

        // Disable the reader and writer before doing anything so that, if using
        // loopback mode, the writer doesn't start sending us the data from the old
        // state of the reader. idk if this is actually necessary
        //
        // i'm not even sure if this works either, there might be data buffered between
        // them. You'd think the `ctrl_reset` would take care of this but it doesn't
        // seem to...
        if let Some(reader) = regs.reader() {
            reader.enable().write([0])?;
        }
        if let Some(writer) = regs.writer() {
            writer.enable().write([0])?;
        }

        // The DMA reader & writer don't actually reset themselves until the next clock edge after they're disabled, so give them a chance to do that.
        thread::sleep(Duration::from_millis(1));

        Ok(Self {
            // TODO: add a builder that allows specifying buffer sizes.
            tx: regs
                .reader()
                .map(|reader_regs| DmaTx::new(litepcie, module, reader_regs, 256 * 8192))
                .transpose()?,
            rx: regs
                .writer()
                .map(|writer_regs| DmaRx::new(litepcie, module, writer_regs, rx_size, 256))
                .transpose()?,
        })
    }
}
