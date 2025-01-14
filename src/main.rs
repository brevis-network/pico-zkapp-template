#![no_main]

pico_sdk::entrypoint!(main);
use pico_sdk::io::read_as;
use pico_sdk::io::commit_bytes;

use alloy_sol_types::SolType;
use alloy_sol_types::sol;

sol! {
    /// The public values encoded as a struct that can be easily deserialized inside Solidity.
    struct PublicValuesStruct {
        uint32 n;
        uint32 a;
        uint32 b;
    }
}

pub fn main() {
    let n: u32 = read_as();
    let mut a: u32 = 0;
    let mut b: u32 = 1;
    for _ in 0..n {
        let c: u32 = a.wrapping_add(b);
        a = b;
        b = c;
    }
    let bytes = PublicValuesStruct::abi_encode(&PublicValuesStruct { n, a, b });

    commit_bytes(&bytes);
}
