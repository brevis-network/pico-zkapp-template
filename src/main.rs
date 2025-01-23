#![no_main]

pico_sdk::entrypoint!(main);
use pico_sdk::io::read_as;
use pico_sdk::io::commit;
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
struct FibonacciData {
    n: i32,
    a: u64,
    b: u64,
}

pub fn main() {
    let n: i32 = read_as();
    let mut a: u64 = 0;
    let mut b: u64 = 1;
    for _ in 0..n {
        let c: u64 = a.wrapping_add(b);
        a = b;
        b = c;
    }
    let data = FibonacciData {
        n,
        a,
        b,
    };
    commit(&data);
}
