use crate::csr::{CsrRo, CsrRw};
use crate::csr_struct;

csr_struct! {
    /// All the CSRs associated with a LitePCIe DMA.
    struct DmaRegisters<'a> {
        /// All the CSRs associated with the DMA's write half (the bit that sends data from the SoC to the host).
        writer: Option<DmaHalfRegisters<'a>>,
        /// All the CSRs associated with the DMA's read half (the bit that receives data from the host).
        reader: Option<DmaHalfRegisters<'a>>,
        /// All the CSRs associated with the DMA's loopback module.
        loopback: Option<DmaLoopbackRegisters<'a>>,
        /// All the CSRs associated with the DMA's buffering module.
        buffering: Option<DmaBufferingRegisters<'a>>,
    }
}

csr_struct! {
    /// All the CSRs associated with the read/write half of a LitePCIe DMA.
    struct DmaHalfRegisters<'a> {
        /// A bitfield:
        /// - Bit 0: Whether this half of the DMA is enabled (writable).
        /// - Bit 1: Whether this half of the DMA is idle.
        enable: CsrRw<'a>,
        /// All the CSRs associated with this half of the DMA's table of descriptors.
        table: DmaTableRegisters<'a>,
    }
}

csr_struct! {
    /// All the CSRs associated with a table of LitePCIe DMA descriptors.
    struct DmaTableRegisters<'a> {
        /// The first 64 bits of the descriptor to write to the table, containing:
        /// - Bits 0-5: Unused.
        /// - Bit 6: `last_disable`, TODO figure out what this does.
        /// - Bit 7: `irq_disable`, TODO figure out what this does (presumably
        ///   disables interrupts when this descriptor is ready to be
        ///   read/written).
        /// - Bits 8-31: `length`, The length of the descriptor (in bytes).
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
        level: CsrRw<'a>,
        /// A CSR which you can write 1 to to reset the table.
        reset: CsrRw<'a>,
    }
}

csr_struct! {
    /// All the CSRs associated with a LiteCPIe DMA's loopback module.
    struct DmaLoopbackRegisters<'a> {
        /// Whether to enable loopback.
        enable: CsrRw<'a>,
    }
}

csr_struct! {
    /// All the CSRs associated with a LiteCPIe DMA's buffering module.
    struct DmaBufferingRegisters<'a> {
        // i'm not using this feature so I can't be bothered to figure out and
        // document what these do.
        reader_fifo_control: CsrRw<'a>,
        reader_fifo_status: CsrRo<'a>,
        writer_fifo_control: CsrRw<'a>,
        writer_fifo_status: CsrRo<'a>,
    }
}
