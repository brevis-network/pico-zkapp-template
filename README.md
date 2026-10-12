# pico-zkapp-template

Minimal Fibonacci-on-Pico example: a guest program that computes a Fibonacci number, and a host
prover that runs it, proves it and verifies the proof.

## Prerequisites

Install the Pico CLI, then the Pico guest toolchain (one time):

```
cargo +nightly-2026-09-27 install --git https://github.com/brevis-network/pico --tag v3.0.0 pico-cli
cargo pico install
```

`nightly-2026-09-27` is the toolchain Pico v3.0.0 builds with on the host, and this repository's
`rust-toolchain` pins the same one for the prover. The guest is built with the `pico` toolchain
that `cargo pico install` sets up; `cargo pico build` selects it for you.

## Quick start

Create a project, build the guest ELF, then run it, prove it and verify the proof:

```
cargo pico new my-app
cd my-app
(cd app && cargo pico build)
cargo run --release -p prover -- execute 100
cargo run --release -p prover -- prove fib.pico 100
cargo run --release -p prover -- verify fib.pico
```

- `cargo pico build` compiles `app/` to `app/elf/riscv64im-pico-zkvm-elf`. Run it again whenever
  `app/` or `lib/` changes.
- `execute 100` runs the guest in the emulator with `n = 100`, without proving it. It takes seconds,
  and nothing it prints is proved, so the guest's output is shown as raw bytes.
- `prove fib.pico 100` proves the guest with `n = 100`, verifies the proof, checks the Fibonacci
  values the guest committed, and writes the proof to `fib.pico`.
- `verify fib.pico` reads the file in a new process, verifies it against the ELF, and prints the
  values the proof commits.

`prove` and `verify` each print the values the proof commits:

```
proved F(100) = (3736710778780434371, 1298777728820984005) and wrote fib.pico
verified fib.pico: the proof commits F(100) = (3736710778780434371, 1298777728820984005)
```

On a 10-core laptop `prove` takes about a minute and peaks at about 6 GB of memory.

## What the proof is

The prover runs in dev mode, and `fib.pico` holds the proof of the RISC-V phase.

- **It verifies in another process, from the ELF alone.** That is what `verify` shows: it holds
  nothing from the run that proved, only the file and `app/elf/riscv64im-pico-zkvm-elf`. The
  values it prints are read from the verified proof, not from bytes stored beside it.
- **It is not an on-chain proof.** A contract verifies a Groth16 proof made in whitelist mode, where
  the same ELF has a different program id. For that flow, start from the `evm` template:
  `cargo pico new --template evm my-app`.
- **It binds the output to a set of separately proved chunks**, not to one complete execution.
  `Prover::prove` goes on to the combine phase, which does, but its result verifies outside the
  process that proved it only against a whitelist.

## Where to change things

| file | what it is |
|---|---|
| `app/src/main.rs` | the guest: reads `n` with `pico_sdk::io::read_as`, commits a `FibonacciData` with `pico_sdk::io::commit` |
| `lib/src/lib.rs` | code the guest and the host share |
| `prover/src/main.rs` | the host: one `Stdin::write` per guest `read_as`, one `proof.committed().read::<T>()` per guest `commit(&T)` |

## AOT mode

The prover can emulate the guest with ahead-of-time compiled code instead of the interpreter. Only
emulation changes: the circuits and the program id are the interpreter's, so the proof verifies
exactly as one made without it, and `verify` needs no AOT code.

```
cargo pico aot --elf app/elf/riscv64im-pico-zkvm-elf --out aot-generated
cargo run --release -p prover --features aot -- prove fib.pico 100
```

- `cargo pico aot` compiles the ELF into the `pico-aot-dispatch` crate in `aot-generated/`, with
  its chunk crates under `aot-generated/chunks/`.
- **Re-run it after every `cargo pico build`.** The generated crate records the SHA-256 of the ELF
  it came from, and the prover refuses one generated from another ELF.
- Before the first `cargo pico aot`, `--features aot` builds against the committed stub, which the
  prover refuses with an error telling you to run `cargo pico aot`.
- The generated crates take `pico-aot-runtime` from the release tag of the `cargo pico` that
  generated them, so use the CLI of the release this template pins (`v3.0.0`). Another tag is a
  second copy of Pico, and the generated code does not build against the prover.
- `aot-generated/` is gitignored apart from the stub, and the generated contents are never
  committed. `git checkout -- aot-generated && rm -rf aot-generated/chunks` restores the stub.
