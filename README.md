# pico-zkapp-template

Minimal Fibonacci-on-Pico example.

## Prerequisites

Install the Pico CLI:

```
cargo +nightly-2025-08-04 install \
  --git https://github.com/brevis-network/pico \
  --tag v2.0.0 \
  pico-cli
```

Install the Pico guest toolchain (one time):

```
cargo pico install
```

## Quick start

Create a project and build the guest ELF:

```
cargo pico new --template basic my-app
cd my-app/app && cargo pico build
```

Prove:

```
cd ../prover
VK_VERIFICATION=false cargo run --release
```

Expected output:

```
Public value n: 100, a: 3314859971, b: 2425370821
```

`VK_VERIFICATION=false` is needed while running stock shapes against a
freshly-built guest ELF on this release.

## AOT mode (experimental)

Opt-in path that drives the snapshot-main thread with the AOT emulator
(`SnapshotMainMode::Aot`) instead of the interpreter. AOT chunks are
generated from your own guest ELF, so the flow has one extra prep step
you re-run whenever `app/src/*.rs` changes.

### One-time setup

Install the AOT codegen binary:

```
cargo +nightly-2025-08-04 install \
  --git https://github.com/brevis-network/pico \
  --tag v2.0.0 \
  pico-aot-codegen
```

### Every time the guest changes

Rebuild the guest ELF, regenerate AOT chunks against it, then prove:

```
cd app && cargo pico build
cd ..

PICO_AOT_RUNTIME_SPEC='git = "https://github.com/brevis-network/pico", tag = "v2.0.0"' \
  generate_crates app/elf/riscv64im-pico-zkvm-elf ./aot-generated

cd prover
VK_VERIFICATION=false cargo run --release --features aot -- --aot
```

`PICO_AOT_RUNTIME_SPEC` tells the codegen tool to emit `pico-aot-runtime`
as a git dep in the generated chunk Cargo.tomls, so `aot-generated/` can
live at the template root without a local pico checkout.

Expected: the console prints
`aot enabled: default_snapshot_main_mode = Aot`
followed by the same `Public value n: 100, ...` line as the default path.

### Notes on AOT mode

- `aot-generated/` is specific to your current guest ELF. If `app/src/*.rs`
  changes, re-run `cargo pico build` and `generate_crates`; otherwise the
  chunks' PC ranges will no longer match and AOT will silently fall back
  to the interpreter.
- `aot-generated/` is gitignored apart from a minimal bootstrap stub.
  Never commit the regenerated contents.
- At larger inputs the AOT path panics at
  `vm/src/emulator/riscv/memory.rs:1013`. Tracked upstream. Does not fire
  at `n = 100`.

## Layout notes

- `app/elf/riscv64im-pico-zkvm-elf` is the default guest ELF, produced by
  `cargo pico build` inside `app/`.
- `app/elf/riscv32im-pico-zkvm-elf` is the historical rv32 ELF, kept for
  reference. The current Pico VM cannot execute it.
