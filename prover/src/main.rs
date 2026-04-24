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

    // Register the AOT factory BEFORE constructing the prover client. The
    // client's DefaultProverClient::new calls EmulatorOpts::default(), which
    // flips snapshot_main to Aot only when the factory is already registered
    // (vm/src/emulator/opts.rs:74).
    #[cfg(feature = "aot")]
    if aot {
        aot_glue::register_with_vm();
        let opts = pico_vm::emulator::opts::EmulatorOpts::default();
        eprintln!(
            "aot enabled: default_snapshot_main_mode = {:?}",
            opts.snapshot_main
        );
    }

    let client = DefaultProverClient::new(&elf);
    let mut stdin_builder = client.new_stdin_builder();

    let n = 100u32;
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
fn verify_public_values(n: u32, public_values: &FibonacciData) {
    println!(
        "Public value n: {:?}, a: {:?}, b: {:?}",
        public_values.n, public_values.a, public_values.b
    );

    let (result_a, result_b) = fibonacci(0, 1, n);

    assert_eq!(result_a, public_values.a, "Mismatch in value 'a'");
    assert_eq!(result_b, public_values.b, "Mismatch in value 'b'");
}
