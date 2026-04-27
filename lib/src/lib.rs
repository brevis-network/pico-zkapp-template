use serde::{Deserialize, Serialize};
use std::fs;

#[derive(Serialize, Deserialize)]
pub struct FibonacciData {
    pub a: u64,
    pub b: u64,
    pub n: u64,
}

/// Computes the Fibonacci sequence starting from `a` and `b` up to the `n`-th iteration.
/// Returns the last two values in the sequence: (a, b).
pub fn fibonacci(mut a: u64, mut b: u64, n: u64) -> (u64, u64) {
    for _ in 0..n {
        let next = a.wrapping_add(b);
        a = b;
        b = next;
    }
    (a, b)
}

/// Loads an ELF file from the specified path.
pub fn load_elf(path: &str) -> Vec<u8> {
    fs::read(path).unwrap_or_else(|err| {
        panic!("Failed to load ELF file from {}: {}", path, err);
    })
}
