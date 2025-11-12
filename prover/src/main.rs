use std::fs;
use fibonacci_lib::load_elf;
use pico_sdk::{client::DefaultProverClient, init_logger};

fn main() {
    // Initialize logger
    init_logger();

    // Load the ELF file
    let elf = load_elf("../app/elf/riscv32im-pico-zkvm-elf");

    // Initialize the prover client
    let client = DefaultProverClient::new(&elf);

    // Write riscv_vk to disk
    let riscv_vk = client.riscv_vk();
    let riscv_vk_bytes = bincode::serialize(&riscv_vk).unwrap();
    fs::write("fibo_riscv_vk.bin", riscv_vk_bytes).unwrap();

    // Initialize new stdin
    let mut stdin_builder = client.new_stdin_builder();

    // Set up input
    let n = 100u32;
    stdin_builder.write(&n);

    // Generate proof
    let (_, proof) = client
        .prove_combine(stdin_builder)
        .expect("Failed to generate proof");

    // Write proof to disk
    let proof_bytes = bincode::serialize(&proof).unwrap();
    std::fs::write("fibo_proof.bin", proof_bytes).unwrap();
}
