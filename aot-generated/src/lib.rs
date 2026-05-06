// Bootstrap stub. Overwritten by `generate_crates` against your current
// guest ELF. Building --features aot WITHOUT having run generate_crates
// first will fail to link because this stub does not export the symbols
// the prover's aot_glue module needs (run_aot, plus the real
// AotEmulatorCore API surface from the dispatch crate).
//
// Fix: run `generate_crates app/elf/riscv64im-pico-zkvm-elf ./aot-generated`
// (see README, "AOT mode" section).
pub use pico_aot_runtime::AotEmulatorCore;
