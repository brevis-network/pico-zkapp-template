use fibonacci_lib::{FibonacciData, fibonacci, load_elf};
use pico_sdk::{client::DefaultProverClient, init_logger};

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

    let n = 100u64;
    stdin_builder.write(&n);

    let proof = client
        .prove_fast(stdin_builder)
        .expect("Failed to generate proof");

    let public_buffer = proof.pv_stream.unwrap();
    let public_values: FibonacciData =
        bincode::deserialize(&public_buffer).expect("Failed to deserialize");

    verify_public_values(n, &public_values);
}

/// Verifies that the computed Fibonacci values match the public values.
fn verify_public_values(n: u64, public_values: &FibonacciData) {
    println!(
        "Public value n: {:?}, a: {:?}, b: {:?}",
        public_values.n, public_values.a, public_values.b
    );

    let (result_a, result_b) = fibonacci(0, 1, n);

    assert_eq!(result_a, public_values.a, "Mismatch in value 'a'");
    assert_eq!(result_b, public_values.b, "Mismatch in value 'b'");
}
