# pico-zkapp-template (EVM)

Fibonacci-on-Pico, through to a proof a Solidity contract verifies: a guest program that computes
a Fibonacci number and commits it ABI-encoded, a host prover for the inner loop, and the contracts
that check the on-chain proof.

## Prerequisites

Install the Pico CLI, then the Pico guest toolchain (one time):

```
cargo +nightly-2026-09-27 install --git https://github.com/brevis-network/pico --tag v3.0.0 pico-cli
cargo pico install
```

`nightly-2026-09-27` is the toolchain Pico v3.0.0 builds with on the host, and this repository's
`rust-toolchain` pins the same one for the prover. The guest is built with the `pico` toolchain
that `cargo pico install` sets up; `cargo pico build` selects it for you.

The on-chain flow also needs [Foundry](https://getfoundry.sh) for the contract tests, and Docker or
a built `pico-gnark` binary for the Groth16 step (below).

## Quick start: build, run and prove locally

```
cargo pico new --template evm my-app
cd my-app
(cd app && cargo pico build)
cargo run --release -p prover -- execute 10
cargo run --release -p prover -- prove fib.pico 10
cargo run --release -p prover -- verify fib.pico
```

- `cargo pico build` compiles `app/` to `app/elf/riscv64im-pico-zkvm-elf`. Run it again whenever
  `app/` or `lib/` changes.
- `execute 10` runs the guest in the emulator with `n = 10`, without proving it. It takes seconds,
  and what it prints is not proved.
- `prove fib.pico 10` proves the guest, verifies the proof, checks the values the guest committed,
  and writes the proof to `fib.pico`. `verify fib.pico` verifies the file in a new process.

```
executed 9632 cycle(s) in 1 chunk(s); the guest committed F(10) = (55, 89), not proved
proved F(10) = (55, 89) and wrote fib.pico
verified fib.pico: the proof commits F(10) = (55, 89)
```

This is the inner loop, in dev mode: `fib.pico` verifies from the ELF in another process, but it is
not a proof a contract can check, and its program id is not the one a contract pins. The on-chain
proof comes from `cargo pico prove --evm`, below.

## The on-chain proof

`cargo pico prove --evm` proves the guest in whitelist mode, wraps the proof, and has gnark prove
the wrap circuit to Groth16. Its `inputs.json` holds what the contract is called with.

```
cd app && cargo pico build && cd ..
# Once, in a checkout of https://github.com/brevis-network/pico at v3.0.0; or set PICO_GNARK_BIN
# to a built pico-gnark binary instead of PICO_GNARK_IMAGE.
docker build -f gnark/Dockerfile -t pico-gnark .

VK_VERIFICATION=true \
MLE_VK_MAP=whitelist/mle_vk_map_kb.bin \
MLE_VK_ROOT="$(sed -n 's/^MLE_VK_ROOT=//p' whitelist/mle_vk_root.txt | tr -d '"')" \
PICO_GNARK_IMAGE=pico-gnark \
  cargo pico prove --elf app/elf/riscv64im-pico-zkvm-elf --input u32:10 \
    --evm --setup --keys keys --output out
cp out/inputs.json contracts/test_data/
cp keys/Groth16Verifier.sol keys/manifest.json contracts/test/dev/
cd contracts && forge test
```

- `whitelist/` is the recursion whitelist of Pico v3.0.0 and its root, the value the release
  publishes. Whitelist mode proves against it, and the wrap circuit bakes its root in.
- The program id the command prints is the one a contract pins: `inputs.json`'s `riscvVKey`, which
  `Fibonacci` takes at deployment. It is the whitelist-mode id, so it differs from the dev-mode id
  `prove` above prints for the same ELF.
- `--setup` makes a Groth16 key set in `keys/`; later proofs for the same circuit reuse it with
  `--keys keys` and no `--setup`.

**The machine.** This is not a laptop flow. On a 124-core machine, the `cargo pico prove --evm`
above, in whitelist mode and including `--setup`, took 5 min 17 s and peaked at 26.8 GiB in
`cargo pico` itself and 15.9 GiB in the gnark container (sampled separately, every 2 s).

### The keys in `contracts/test/dev` are test keys

`--setup` runs a Groth16 setup on your machine, which knows the setup's randomness: anyone holding
it can forge proofs that verify. `contracts/test/dev/Groth16Verifier.sol` and its `manifest.json`
come from such a setup and are for tests only. Never deploy a verifier made from them.

## The contracts

| file | what it is |
|---|---|
| `contracts/src/IPicoVerifier.sol` | `verifyPicoProof(bytes32 riscvVkey, bytes publicValues, uint256[12] proof)`, which reverts unless the proof verifies |
| `contracts/src/PicoVerifier.sol` | hashes the public values and calls a Groth16 verifier, whose address it is deployed with |
| `contracts/src/Fibonacci.sol` | the app: pins one program id, verifies a proof through `IPicoVerifier`, and decodes `(n, a, b)` |
| `contracts/test/Fibonacci.t.sol` | deploys the three over the test keys: the proof in `test_data/inputs.json` gives `(10, 55, 89)`, and a zero proof, changed public values or another program id revert with `ProofInvalid()` |

The proof is twelve words: the Groth16 proof (8), a Pedersen commitment (2) and its proof of
knowledge (2), in the order `inputs.json` lists them. The tests need nothing installed beyond
Foundry.

## Where to change things

| file | what it is |
|---|---|
| `app/src/main.rs` | the guest: reads `n` with `pico_sdk::io::read_as`, commits the ABI-encoded `PublicValuesStruct` with `pico_sdk::io::commit_bytes` |
| `lib/src/lib.rs` | code the guest and the host share, `PublicValuesStruct` among it |
| `prover/src/main.rs` | the host: one `Stdin::write` per guest `read_as`, and the committed bytes decoded as `PublicValuesStruct` |

## AOT mode

The prover can emulate the guest with ahead-of-time compiled code instead of the interpreter. Only
emulation changes: the circuits and the program id are the interpreter's, so the proof verifies
exactly as one made without it, and `verify` needs no AOT code.

```
cargo pico aot --elf app/elf/riscv64im-pico-zkvm-elf --out aot-generated
cargo run --release -p prover --features aot -- prove fib.pico 10
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
