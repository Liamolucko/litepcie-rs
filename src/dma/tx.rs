use core::slice;
use std::collections::VecDeque;
use std::io::{self, Write};
use std::iter::ExactSizeIterator;
use std::mem::MaybeUninit;
use std::ops::Range;
use std::sync::atomic::{fence, Ordering};
use std::thread;
use std::time::Duration;

use crate::{IovaRange, Irq, LitePcie};

use super::DmaHalfRegisters;

/// A ring buffer for sending data to the SoC.
#[derive(Debug)]
pub struct DmaTx<'a> {
    regs: DmaHalfRegisters<'a>,
    /// An interrupt the SoC fires whenever it finishes processing a descriptor
    /// for which `irq_disable` is 0.
    irq: Irq<'a>,

    buf: IovaRange<'a>,
    /// The number of bytes we send to the FPGA before requiring it to tell us
    /// once it's read them.
    ///
    /// More specifically, every `chunk_size`th byte in `buf` is marked as
    /// special, and whenever a write to the buffer crosses that byte, we send a
    /// descriptor ending at that byte to the FPGA with interrupts enabled.
    ///
    /// So if `chunk_size` was 4, the buffer would look like this:
    ///
    /// ```text
    /// ---x---x---x...
    /// ```
    ///
    /// If you write 1 byte, it just gets added to the buffer and nothing
    /// happens.
    ///
    /// If you then write an extra 4 bytes, the buffer looks like this:
    ///
    /// ```text
    /// dddxd--x---x...
    /// ```
    ///
    /// A descriptor for the first 4 bytes then get sent to the FPGA, while the
    /// 5th byte stays in the buffer unwritten.
    ///
    /// One past the end of `buf` is also treated as a special byte; we send out
    /// a descriptor with interrupts enabled if writing hits the end of `buf`.
    ///
    /// Calling `flush` triggers a descriptor to be sent out early, this time
    /// with interrupts disabled.
    chunk_size: usize,

    /// What `DmaTableRegisters::loop_status` was last time we checked. Note
    /// that we always use prog mode, so this is the number of descriptors the
    /// DMA reader's processed since reset.
    last_loop_status: u32,
    /// For each descriptor that's still in-flight, the end of the range in
    /// `buf` it covers (exclusive).
    descriptor_ends: VecDeque<usize>,
    /// The start of the range in `buf` that isn't in use by any descriptors
    /// (inclusive).
    ///
    /// This must always be within `0..self.buf.len()`.
    free_start: usize,
    /// The end of the range in `buf` that isn't in use by any descriptors
    /// (exclusive).
    ///
    /// This and `free_start` aren't just a normal range because they can wrap
    /// around the end of `buf` and stop being a valid range.
    ///
    /// This must always be within `0..self.buf.len()`, except when the entire
    /// buffer is free: then `free_start` should be 0, and `free_end` should be
    /// `self.buf.len()`.
    free_end: usize,
}

impl<'a> DmaTx<'a> {
    /// Makes a new `DmaTx` with the given capacity.
    pub(crate) fn new(
        litepcie: &'a LitePcie<'a>,
        module: &str,
        regs: DmaHalfRegisters<'a>,
        capacity: usize,
    ) -> crate::Result<Self> {
        assert!(
            capacity % 4 == 0,
            "LitePCIe only supports sending/receiving chunks of data whose sizes are multiples of \
             4 bytes"
        );

        // Reset the DMA reader's descriptor table.
        regs.table().reset().write([1])?;
        // Set the table to prog mode.
        regs.table().loop_prog_n().write([0])?;

        let irq = litepcie.irq(&format!("{module}_reader"))?;
        // Enable interrupts when a descriptor's completed.
        irq.enable()?;

        // Enable the reader.
        regs.enable().write([1])?;
        Ok(Self {
            regs,

            // Note that 'reader' here means the one in the SoC, which is reading the stuff we're
            // writing.
            irq,
            // TODO: throw an error if this goes over 32 bits and the DMA is using 32-bit addresses.
            buf: litepcie.alloc_iova_range(capacity)?,
            // I'm mimicking how often the official LitePCIe driver triggers interrupts here: it has
            // 256 write buffers and triggers an interrupt on every 32nd one, so every time 1/8th of
            // its capacity is read.
            //
            // It also has to be able to fit in 24 bits though, since that's the biggest that a
            // descriptor can be.
            chunk_size: usize::min((capacity / 8).next_multiple_of(4), (1 << 24) - 1),
            // We reset the descriptor tables on startup, and so the initial `loop_status` should
            // always be 0.
            last_loop_status: 0,
            descriptor_ends: VecDeque::new(),
            free_start: 0,
            free_end: capacity,
        })
    }

    /// Updates the buffer with the new number of descriptors the SoC has
    /// processed, so that it can mark the space in the buffer they were
    /// referencing as free.
    fn update(&mut self) -> io::Result<()> {
        let [loop_status] = self.regs.table().loop_status().read()?;
        // If `loop_status` overflows, we can end up with `loop_status <
        // self.last_loop_status`; in that case we want to do wrapping subtraction.
        let descriptors_processed = loop_status.wrapping_sub(self.last_loop_status);
        let descriptors_processed: usize = descriptors_processed.try_into().unwrap();
        self.last_loop_status = loop_status;

        if let Some(index) = self.descriptor_ends.drain(..descriptors_processed).last() {
            self.free_end = index;
            if self.free_end == self.buf.len() {
                // We always represent this as 0, unless the whole buffer's free (which we check
                // for in a second).
                self.free_end = 0;
            }
            if self.free_end == self.free_start {
                // We've just freed up the whole buffer; reset the range to `0..self.buf.len()`,
                // otherwise `free_start == free_end` will now represent no free space.
                self.free_start = 0;
                self.free_end = self.buf.len();
            }
        }

        Ok(())
    }

    /// Returns the range in `self.buf` that data's been written to but we
    /// haven't sent a descriptor out for yet.
    fn buffered(&self) -> Range<usize> {
        let mut start = self
            .descriptor_ends
            .back()
            .copied()
            .unwrap_or(self.free_end);
        let mut end = self.free_start;

        if start == self.buf.len() {
            start = 0;
        }
        if end == 0 && start != 0 {
            end = self.buf.len();
        }

        // This should always hold; the buffered area can't wrap around the end of
        // `self.buf` because we send out a descriptor if that happens.
        debug_assert!(start <= end);

        start..end
    }

    /// Returns the first contiguous piece of our buffer's free space (space
    /// that isn't currently part of `buffered` or covered by a descriptor).
    fn free(&self) -> Range<usize> {
        if self.free_start <= self.free_end {
            // The whole free area is contiguous.
            self.free_start..self.free_end
        } else {
            // The free area wraps around the end of the buffer, so we just return the first
            // part.
            self.free_start..self.buf.len()
        }
    }

    /// Add a descriptor to the reader on the FPGA's table, telling it to read
    /// the given range of bytes (in `self.buf`) and optionally send an
    /// interrupt when it's done.
    fn add_descriptor(&mut self, range: Range<usize>, irq: bool) -> io::Result<()> {
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
        self.regs.table().we().write([(address >> 32) as u32])?;
        self.descriptor_ends.push_back(range.end);
        Ok(())
    }
}

impl<'a> Write for DmaTx<'a> {
    fn write<'b>(&mut self, buf: &'b [u8]) -> io::Result<usize> {
        if buf.is_empty() {
            return Ok(0);
        }

        // First, copy from `buf` into our buffer.
        // If there's no free space wait for some to open up.
        if self.free().is_empty() {
            self.update()?;
            while self.free().is_empty() {
                // TODO: I couldn't get interrupts to work, so for now we just busy-wait.
                // self.irq.wait()?;
                self.update()?;
            }
        }
        let free = self.free();

        let copy_len = usize::min(buf.len(), free.len());
        // In order to make use of `copy_from_slice` we need to first convert `buf` into
        // a `&'b [MaybeUninit<u8>]`.
        let buf_uninit: &'b [MaybeUninit<u8>] =
            unsafe { slice::from_raw_parts(buf.as_ptr() as *const MaybeUninit<u8>, buf.len()) };
        unsafe {
            self.buf
                .slice_mut(free.start..free.start + copy_len)
                .copy_from_slice(&buf_uninit[..copy_len])
        }

        // Make sure the FPGA can see the data we wrote.
        // (I'm not 100% sure if this is actually necessary.)
        fence(Ordering::Release);

        self.free_start = free.start + copy_len;
        if self.free_start == self.buf.len() {
            self.free_start = 0;
            if self.free_end == self.buf.len() {
                // We've just shrunk the amount of free space, so if `self.free_start` has met
                // up with `self.free_end` at `self.buf.len()` that means there's now no free
                // space and we should represent that with `0..0`.
                self.free_end = 0;
            }
        }

        while self.buffered().start / self.chunk_size != self.buffered().end / self.chunk_size
            || !self.buffered().is_empty() && self.buffered().end == self.buf.len()
        {
            // A new chunk of our buffer is fully filled in and ready for the FPGA to read;
            // tell it as much.
            self.add_descriptor(
                self.buffered().start
                    ..usize::min(self.buffered().start + self.chunk_size, self.buffered().end),
                true,
            )?;
        }

        Ok(copy_len)
    }

    fn flush(&mut self) -> io::Result<()> {
        assert!(
            self.buffered().len() % 4 == 0,
            "LitePCIe only supports sending/receiving chunks of data whose sizes are multiples of \
             4 bytes"
        );
        self.add_descriptor(self.buffered(), false)
    }
}

impl Drop for DmaTx<'_> {
    fn drop(&mut self) {
        self.irq.disable().unwrap();
        self.regs.table().reset().write([1]).unwrap();
        thread::sleep(Duration::from_millis(1));
        self.regs.enable().write([0]).unwrap();
        self.regs.table().reset().write([1]).unwrap();
    }
}

// TODO: add destructor.
