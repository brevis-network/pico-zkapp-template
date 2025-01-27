use pico_sdk::{init_logger, client::SDKProverClient};
fn main() {
    init_logger();
    let elf: &[u8] = include_bytes!("../../elf/riscv32im-pico-zkvm-elf");
    let inputs = 10u32.to_le_bytes();
    let client = SDKProverClient::new(elf, &inputs);
    let proof = client.prove_fast().unwrap();
    // TODO: provide client.verify, or verify the proof in prove_fast() / prove()?
    // TODO: save proof in json & use alloy to decode and print the public values
    println!("inputs bytes: {:02x?}", inputs);
}
