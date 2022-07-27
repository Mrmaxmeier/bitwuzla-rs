// this ensures that crate users generating docs with --no-deps will still
// properly get links to the public docs for bitwuzla's types
#![doc(html_root_url = "https://docs.rs/bitwuzla/0.4.2")]

mod btor;
pub use btor::Btor;
pub use btor::{Bitwuzla, SolverResult};
mod node;
pub use node::Array;
pub use node::BVSolution;
pub use node::BV;
pub mod option;
mod sort;
mod timeout;
