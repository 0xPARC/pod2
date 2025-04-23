pub mod falcon;
pub mod falcon_circuit;
mod falcon_lib;
pub mod proofbased;
pub mod proofbased_circuit;

// expose proofbased as the main signature scheme
pub use proofbased::*;
pub use proofbased_circuit::*;
