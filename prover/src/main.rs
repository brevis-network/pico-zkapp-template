use anyhow::{bail, Context, Result};
use pico_sdk::{client::DefaultProverClient, init_logger};
use std::{fs, path::PathBuf};

#[cfg(feature = "aot")]
mod aot_glue;

const AVAILABLE_BLOCKS: &[u32] = &[18884864];
const DEFAULT_BLOCK: u32 = 18884864;

fn main() -> Result<()> {
    init_logger();

    let aot = std::env::args().any(|a| a == "--aot");
    let block = parse_block_arg();

    #[cfg(not(feature = "aot"))]
    if aot {
        eprintln!(
            "--aot was passed but the `aot` feature is not enabled. \
            Rebuild with `cargo run --features aot -p prover -- --aot`."
        );
        std::process::exit(2);
    }

    validate_block(block)?;
    let block_input = load_block_input(block)?;
    println!(
        "Proving reth block {} (input {} bytes)",
        block,
        block_input.len()
    );

    // Both default and AOT paths run the template's own rv64 guest ELF.
    // aot-generated/ must have been populated from this same ELF via
    // `generate_crates` beforehand when --aot is used; see README.
    let elf = load_elf("../app/elf/riscv64im-pico-zkvm-elf")?;

    #[cfg(feature = "aot")]
    let client = if aot {
        aot_glue::register_with_vm();
        let opts = pico_vm::emulator::opts::EmulatorOpts::default()
            .with_snapshot_main(pico_vm::emulator::opts::SnapshotMainMode::Aot);
        DefaultProverClient::new_with_opts(&elf, opts)
    } else {
        DefaultProverClient::new(&elf)
    };

    #[cfg(not(feature = "aot"))]
    let client = DefaultProverClient::new(&elf);

    let mut stdin_builder = client.new_stdin_builder();
    // Raw passthrough: fixture is already bincode-serialized
    // EthClientExecutorInput; the guest deserializes via read_vec().
    stdin_builder.write_slice(&block_input);

    let proof = client
        .prove_fast(stdin_builder)
        .expect("Failed to generate proof");

    let public_buffer = proof.pv_stream.expect("missing public values");
    println!(
        "Proof produced. Public-value buffer: {} bytes",
        public_buffer.len()
    );

    Ok(())
}

fn parse_block_arg() -> u32 {
    std::env::args()
        .skip(1)
        .find(|a| !a.starts_with("--"))
        .and_then(|s| s.parse().ok())
        .unwrap_or(DEFAULT_BLOCK)
}

fn validate_block(block: u32) -> Result<()> {
    let path = block_input_path(block);
    if !path.exists() {
        bail!(
            "Block {} input file not found.\nKnown blocks (require fixture file): {:?}\nExpected path: {}\n\
             Drop a bincode-serialized EthClientExecutorInput at that path to add a new block.",
            block,
            AVAILABLE_BLOCKS,
            path.display()
        );
    }
    Ok(())
}

fn workspace_relative_path(rel: &str) -> PathBuf {
    let p = std::path::Path::new(rel);
    if p.exists() {
        return p.to_path_buf();
    }
    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    std::path::Path::new(manifest_dir)
        .parent()
        .map(|w| w.join(rel))
        .unwrap_or_else(|| p.to_path_buf())
}

fn block_input_path(block: u32) -> PathBuf {
    workspace_relative_path(&format!("fixtures/reth-{}.bin", block))
}

fn load_block_input(block: u32) -> Result<Vec<u8>> {
    let path = block_input_path(block);
    fs::read(&path).with_context(|| format!("failed to read block input from {}", path.display()))
}

fn load_elf(rel: &str) -> Result<Vec<u8>> {
    let path = workspace_relative_path(rel);
    fs::read(&path).with_context(|| format!("failed to read guest ELF from {}", path.display()))
}
