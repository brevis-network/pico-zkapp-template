use fibonacci_lib::load_elf;
use pico_sdk::{client::DefaultProverClient, init_logger};
use std::env;

#[cfg(feature = "aot")]
mod aot_glue;

fn main() {
    init_logger();

    let aot = std::env::args().any(|a| a == "--aot");

    #[cfg(not(feature = "aot"))]
    if aot {
        eprintln!(
            "--aot was passed but the `aot` feature is not enabled. \
            Rebuild with `cargo run --features aot -p prover -- --aot`."
        );
        std::process::exit(2);
    }

    // Both default and AOT paths run the template's own rv64 guest ELF.
    // aot-generated/ must have been populated from this same ELF via
    // `generate_crates` beforehand when --aot is used; see README.
    let elf = load_elf("../app/elf/riscv64im-pico-zkvm-elf");

    #[cfg(feature = "aot")]
    let client = if aot {
        // Register the AOT factory, then construct the client with
        // SnapshotMainMode::Aot explicitly selected. The SDK no longer
        // auto-flips the default based on registration state — callers opt
        // in through EmulatorOpts so the AOT path is never taken by accident.
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

    let n = 10u32;
    stdin_builder.write(&n);

    let current_dir = env::current_dir().expect("Failed to get current directory");
    let output_path = current_dir.join("../contracts/test_data");

    // Set up groth16 verifier and generate pico proof
    // The first parameter `need_setup = true` ensures the Groth16 verifier is set up,
    // but this setup is required only once.
    client
        .prove_evm(stdin_builder, true, output_path.clone(), "kb")
        .expect("Failed to generate evm proof");
}
