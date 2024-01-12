use pci_driver::regions::structured::PciRegisterRw;
use pci_driver::{pci_bit_field, pci_struct};

mod soc_info;
pub use soc_info::*;

pub use pci_driver;

/// A macro similar to `pci_driver::pci_struct` for defining groups of LiteX
/// CSRs.
///
/// The main difference is that instead of hardcoding the offsets of all the
/// fields, it looks them up from an `SocInfo`.
///
/// This means that it can't implement `BackedByPciSubregion` directly, since
/// there's no way to pass it an `SocInfo` through that trait.
#[macro_export]
macro_rules! csr_struct {
    (
        $(
            $(#[$attr:meta])*
            $vis:vis struct $name:ident<$lifetime:lifetime> {
                $(
                    $(#[$field_attr:meta])*
                    $field_name:ident: $field_ty:ty
                ),* $(,)?
            }
        )*
    ) => {
        $(#[$attr])*
        $vis struct $name<$lifetime> {
            region: $crate::pci_driver::regions::PciSubregion<'a>,
            $($field_name: u64,)*
        }

        impl<$lifetime> $name<lifetime> {
            $vis fn new(region: impl $crate::pci_driver::regions::AsPciSubregion<'a>, soc_info: &$crate::SocInfo, module: &str) -> Result<Self, $crate::Error> {}
        }
    };
}

/// A trait for values that can be used as the type parameter in a `Csr`.
pub trait CsrValue {
    /// The number of bytes this type takes up.
    ///
    /// If this isn't a multiple of `config_csr_data_width` (usually 4), the
    /// size of the CSR is rounded up to the nearest multiple of it.
    const BYTES: u64;

    /// Creates a copy of `Self` from the given bytes read from a CSR.
    ///
    /// `bytes` is always `Self::BYTES` long, Rust just doesn't allow writing
    /// fixed-length arrays whose lengths are an associated type of a trait
    /// right now.
    fn from_bytes(bytes: &[u8]) -> Self;
    /// Writes `self` into `bytes`, which will then be written into a CSR.
    ///
    /// `bytes` is always `Self::BYTES` long, Rust just doesn't allow writing
    /// fixed-length arrays whose lengths are an associated type of a trait
    /// right now.
    fn write_bytes(self, bytes: &mut [u8]);
}

pci_struct! {
    struct DmaRegisters<'a> {
        writer    @ 0x00 : DmaHalfRegisters<'a>,
        reader    @ 0x20 : DmaHalfRegisters<'a>,
        loopback  @ 0x40 : DmaLoopbackRegisters<'a>,
        buffering @ 0x44 : DmaBufferingRegisters<'a>,
    }
}

pci_struct! {
    struct DmaHalfRegisters<'a> {
        enable @ 0x00 : DmaHalfEnable<'a>,
        table  @ 0x04 : DmaTableRegisters<'a>,
    }
}

pci_bit_field! {
    struct DmaHalfEnable<'a> : RW u32 {
        enable @ 0 : RW,
        idle   @ 1 : RO,
    }
}

pci_struct! {
    struct DmaTableRegisters<'a> {
        /// The first 32 bits of the descriptor to write to the table, containing:
        /// - Bits 0-5: Unused.
        /// - Bit 6: `last_disable`, TODO figure out what this does.
        /// - Bit 7: `irq_disable`, TODO figure out what this does (presumably disables
        ///   interrupts when this descriptor is ready to be read/written).
        /// - Bits 8-31: `length`, The length of the descriptor (in bytes).
        value_lo @ 0x00 : PciRegisterRw<'a, u32>,
        /// The next 32 bits of the descriptor to write, which are the low 32 bits of
        /// the address in the CPU's memory to read/write from.
        value_hi @ 0x04 : PciRegisterRw<'a, u32>,
        /// The final 32 bits of the descriptor to write, which are the high 32 bits of
        /// the address in the CPU's memory to read/write from.
        ///
        /// Writing to this register triggers the whole descriptor to be added to the
        /// table (hence why it's called 'write-enable' instead of just `value3` or
        /// something).
        we       @ 0x08 : PciRegisterRw<'a, u32>,
    }
}

pci_struct! {
    struct DmaLoopbackRegisters<'a> {}
}

pci_struct! {
    struct DmaBufferingRegisters<'a> {}
}
