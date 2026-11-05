//! Run the fibonacci guest through the host prover: emulate it, prove it, and verify the proof in
//! another process.
//!
//! ```text
//! (cd app && cargo pico build)
//! cargo run --release -p prover -- execute 100
//! cargo run --release -p prover -- prove fib.pico 100
//! cargo run --release -p prover -- verify fib.pico
//! ```
//!
//! `execute` prints the guest's output undecoded: nothing has been proved, and only a verified
//! proof hands out the committed values to decode.
//!
//! With the `aot` feature, `execute` and `prove` emulate with the guest's AOT-compiled code, which
//! `cargo pico aot` generates into `aot-generated/`. Only emulation changes: the circuits and the
//! program id are the interpreter's, so `verify` needs no AOT code.
//!
//! This runs in dev mode: no whitelist, natural trace heights. The same ELF has a different program
//! id under `verify_keys(true)`, and that is the id a contract pins.
//!
//! The file holds the RISC-V proof because that is the phase a process that proved nothing can
//! verify from the ELF alone. The combine root that `Prover::prove` returns verifies outside the
//! process that produced it only against the whitelist. The price is the weaker statement: a
//! RISC-V proof binds the output to a set of separately proved chunks, not to one complete
//! execution (`Proof::binds_complete_execution`).

use std::{error::Error, process::ExitCode};

use fibonacci_lib::{FibonacciData, fibonacci};
use pico_prover::{Phase, Proof, ProofArtifact, Prover, ProverBuilder, Stdin};

/// Where `cargo pico build` writes the guest.
const ELF_PATH: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../app/elf/riscv64im-pico-zkvm-elf"
);

const DEFAULT_N: u64 = 100;

const USAGE: &str = "usage: prover execute [n] | prove <proof-file> [n] | verify <proof-file>";

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("error: {e}");
            ExitCode::FAILURE
        }
    }
}

fn run() -> Result<(), Box<dyn Error>> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let args: Vec<&str> = args.iter().map(String::as_str).collect();
    let elf = std::fs::read(ELF_PATH)
        .map_err(|e| format!("{ELF_PATH}: {e}; build the guest with `cargo pico build` in app/"))?;

    // Each arm reads its arguments before keygen, which takes seconds.
    match args.as_slice() {
        ["execute", n @ ..] => {
            // Emulation only, without keygen: seconds, and nothing is proved.
            let n = parse_n(n)?;
            let execution = builder(&elf).execute(Stdin::from(&n))?;
            println!(
                "executed {} cycle(s) in {} chunk(s); the guest committed {} byte(s), not proved: {}",
                execution.cycles,
                execution.chunks,
                execution.committed_bytes.len(),
                hex(&execution.committed_bytes)
            );
        }
        ["prove", path, n @ ..] => {
            let n = parse_n(n)?;
            let mut prover = builder(&elf).build()?;
            let proof = prover.prove_to(Stdin::from(&n), Phase::Riscv)?;
            let values = check(&proof, Some(n))?;
            proof.write(path)?;
            println!(
                "proved F({}) = ({}, {}) and wrote {path}",
                values.n, values.a, values.b
            );
            report(&proof);
        }
        ["verify", path] => {
            let artifact = ProofArtifact::read(path)?;
            let prover = Prover::new(&elf)?;
            let proof = prover.verify_artifact(artifact)?;
            let values = check(&proof, None)?;
            println!(
                "verified {path}: the proof commits F({}) = ({}, {})",
                values.n, values.a, values.b
            );
            report(&proof);
        }
        _ => return Err(USAGE.into()),
    }
    Ok(())
}

/// The options `execute` and `prove` emulate with.
fn builder(elf: &[u8]) -> ProverBuilder {
    let builder = Prover::builder(elf);
    #[cfg(feature = "aot")]
    let builder = builder.aot(&pico_aot_dispatch::AOT);
    builder
}

fn parse_n(args: &[&str]) -> Result<u64, Box<dyn Error>> {
    match args {
        [] => Ok(DEFAULT_N),
        [n] => Ok(n.parse().map_err(|e| format!("n = `{n}`: {e}"))?),
        _ => Err(USAGE.into()),
    }
}

/// Read the one `FibonacciData` the guest commits from the verified proof, and hold it to the
/// sequence recomputed here. Bytes left over after it are refused: the guest commits nothing else.
/// `asked` is the `n` this process gave the guest, if it gave one.
fn check(proof: &Proof, asked: Option<u64>) -> Result<FibonacciData, Box<dyn Error>> {
    let mut committed = proof.committed();
    let values: FibonacciData = committed.read()?;
    if !committed.remaining().is_empty() {
        return Err(format!(
            "the guest commits {} byte(s) after its FibonacciData",
            committed.remaining().len()
        )
        .into());
    }
    if let Some(asked) = asked.filter(|&asked| asked != values.n) {
        return Err(format!(
            "the guest commits F({}), not the F({asked}) it was given",
            values.n
        )
        .into());
    }
    let (a, b) = fibonacci(0, 1, values.n);
    if (values.a, values.b) != (a, b) {
        return Err(format!(
            "the guest commits F({}) = ({}, {}), not ({a}, {b})",
            values.n, values.a, values.b
        )
        .into());
    }
    Ok(values)
}

/// Both commands that print this run in dev mode, and `verify_artifact` refuses a file from the
/// other mode.
fn report(proof: &Proof) {
    if !proof.binds_complete_execution() {
        eprintln!(
            "note: a {} proof binds each chunk, not one complete execution",
            proof.phase()
        );
    }
    println!(
        "program id (dev mode, not the id an on-chain verifier pins): {}",
        proof.program_id()
    );
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}
