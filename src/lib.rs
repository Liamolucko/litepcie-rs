mod soc_info;
pub use soc_info::*;

pub mod csr;
pub mod dma;

pub use pci_driver;
#[doc(hidden)]
pub use std;

#[derive(thiserror::Error, Debug, Clone)]
pub enum Error {
    #[error("required CSR `{csr}` not found in SocInfo")]
    MissingCsr { csr: String },
    #[error("expected CSR `{csr}` of size {expected}, found {found}")]
    CsrWrongSize {
        csr: String,
        expected: u64,
        found: u64,
    },
    #[error("expected CSR `{csr}` to be {expected}, but it was {found}")]
    CsrWrongKind {
        csr: String,
        expected: CsrKind,
        found: CsrKind,
    },
}

pub type Result<T> = std::result::Result<T, Error>;
