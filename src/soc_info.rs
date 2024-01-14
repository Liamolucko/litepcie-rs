use std::borrow::Cow;
use std::collections::HashMap;
use std::fmt::{self, Display, Formatter};

use serde::{Deserialize, Serialize};

/// Information about a LiteX SoC, mainly the the addresses of all its CSRs.
///
/// To create an `SocInfo` for your SoC, you need to call
/// `litex.soc.integration.export.get_csr_json` in Python, and then parse the
/// JSON it returns into this struct (probably using `include_str!` to include
/// it in the binary).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SocInfo<'a> {
    /// A map from the name of every LiteX module that has CSRs to the address
    /// where those CSRs start.
    ///
    /// Those addresses are addresses on the SoC's main bus, which are mapped
    /// directly to addresses in its PCIe BAR 0.
    pub csr_bases: HashMap<Cow<'a, str>, u64>,
    /// A map from the name of every CSR in the SoC to information about it.
    ///
    /// The name of a CSR is formatted as `<module>_<submodule1>_..._<csr>`,
    /// where:
    /// - `module` is the name of the module the CSR belongs in.
    /// - `submodule<n>` is the name of the `n`th submodule between `module` and
    ///   the module where the CSR's defined.
    /// - `csr_name` is the name of the CSR.
    ///
    /// It seems like the distinction between a module that shows up in
    /// `csr_bases` and a submodule that just gets added to the name is that
    /// modules are created with `self.add_module("name", module)`, and
    /// submodules are created with `self.name = module`; but I'm not an expert
    /// on Migen/LiteX so I'm not entirely sure.
    pub csr_registers: HashMap<Cow<'a, str>, CsrInfo>,
    /// A map from the names of constants about the SoC to their values.
    ///
    /// `None` is used for boolean constants: not being in the map means
    /// `false`, and `None` means `true`, similar to `#define`s in C.
    pub constants: HashMap<Cow<'a, str>, Option<SocConstant<'a>>>,
    /// A map from the names of regions of the SoC's memory to info about them.
    pub memories: HashMap<Cow<'a, str>, MemoryRegion<'a>>,
}

/// Information about an individual CSR.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct CsrInfo {
    /// The address of the register.
    ///
    /// Same as [`SocInfo::csr_bases`], these are addresses on the SoC's
    /// main bus.
    pub addr: u64,
    /// The number of `u32`s this CSR takes up.
    ///
    /// In theory it's actually in units of `config_csr_data_width` (one of the
    /// values in [`SocInfo::constants`]), but [LiteX doesn't let you set that
    /// to anything other than 32 bits if you're using PCIe
    /// anyway][csr_32bit_check].
    ///
    /// [csr_32bit_check]: https://github.com/enjoy-digital/litex/blob/6b79644/litex/soc/integration/soc.py#L2133
    pub size: u64,
    /// Whether the CSR is read-only or read-write.
    #[serde(rename = "type")]
    pub kind: CsrKind,
}

/// Whether a CSR is read-only or read-write.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum CsrKind {
    /// The CSR can only be read from.
    #[serde(rename = "ro")]
    ReadOnly,
    /// The CSR can be both read and written.
    #[serde(rename = "rw")]
    ReadWrite,
}

impl Display for CsrKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            CsrKind::ReadOnly => f.pad("read-only"),
            CsrKind::ReadWrite => f.pad("read-write"),
        }
    }
}

/// The value of a constant about an SoC, which can either be a string or an
/// integer.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(untagged)]
pub enum SocConstant<'a> {
    String(Cow<'a, str>),
    // I picked an `i32` for the type here because these constants are also sometimes returned by
    // getter functions in C, and LiteX uses a C `int` as the return value for those functions
    // when the constant is an integer.
    Integer(i32),
}

/// Information about a region of the SoC's memory.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct MemoryRegion<'a> {
    /// The address where the memory region starts.
    ///
    /// Same as [`SocInfo::csr_bases`], these are addresses on the SoC's
    /// main bus.
    pub base: u64,
    /// The size of the memory region, in bytes.
    pub size: u64,
    /// What kind of region this is.
    ///
    /// This is either `"cached"`, `"io"`, or either of the two with `+linker`
    /// added onto the end.
    #[serde(rename = "type")]
    pub kind: Cow<'a, str>,
}
