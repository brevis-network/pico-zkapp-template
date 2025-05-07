use fibonacci_lib::load_elf;
use pico_sdk::{client::DefaultProverClient, init_logger};
use std::env;

fn main() {
    // Initialize logger
    init_logger();

    // Load the ELF file
    let elf = load_elf("../elf/riscv32im-pico-zkvm-elf");

    // Initialize the prover client
    let client = DefaultProverClient::new(&elf);
    // Initialize new stdin
    let mut stdin_builder = client.new_stdin_builder();

    // Set up input
    let n = 10u32;
    stdin_builder.write(&n);

    // Set up output path
    let current_dir = env::current_dir().expect("Failed to get current directory");
    let output_path = current_dir.join("../contracts/test_data");

    // Set up groth16 verifier and generate pico proof
    // The first parameter `need_setup = true` ensures the Groth16 verifier is set up,
    // but this setup is required only once.
    client
        .prove_evm(stdin_builder, true, output_path.clone(), "kb")
        .expect("Failed to generate evm proof");
}
