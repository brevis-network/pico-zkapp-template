use fibonacci_lib::load_elf;
use pico_sdk::{init_logger, vk_client::BabyBearProveVKClient};
use std::env;

fn main() {
    // Initialize logger
    init_logger();

    // Load the ELF file
    let elf = load_elf("../elf/riscv32im-pico-zkvm-elf");

    // Initialize the prover client
    let client = BabyBearProveVKClient::new(&elf);
    let stdin_builder = client.get_stdin_builder(); // Shared instance

    // Set up input
    let n = 10u32;
    stdin_builder.borrow_mut().write(&n);

    // Set up output path
    let current_dir = env::current_dir().expect("Failed to get current directory");
    let output_path = current_dir.join("../contracts/test_data");

    // Set up groth16 verifier and generate pico proof
    // The first parameter `need_setup = true` ensures the Groth16 verifier is set up,
    // but this setup is required only once.
    client
        .prove_evm(true, output_path.clone())
        .expect("Failed to generate proof");
}
