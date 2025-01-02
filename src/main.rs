#![no_main]
pico_entry::entrypoint!(main);

pub fn main() {
    let n = 10;
    let mut a: u64 = 0;
    let mut b: u64 = 1;
    for _ in 0..n {
        let c: u64 = a.wrapping_add(b);
        a = b;
        b = c;
    }
    println!("a: {}, b: {}", a, b);
}
