# Comet Sunbeam verification

This directory contains verification-only Certora Sunbeam configuration. Normal contract builds do not enable the `certora` feature and therefore exclude the rules and CVLR dependencies from deployed WASM. The narrower `certora-storage-symbols` feature additionally replaces the pool's no-payload `DataKey` serialization with an injective short-symbol encoding; it is a conditional verifier abstraction, not a deployment feature.

## Pinned compatibility set

| Component | Pin | Reason |
| --- | --- | --- |
| Rust | `1.92.0` | Repository `rust-toolchain.toml` |
| Java | Temurin JRE `21.0.12.1+1` | Local Apple Silicon cache used for the compatibility spike |
| Soroban SDK | `25.3.2` | Workspace dependency |
| Certora CLI | `8.19.1` | Python dependency in `requirements.txt` |
| CVLR assertions | `0.6.1` | Exact `no_std` optional dependency; the umbrella `cvlr` crate includes `cvlr-spec`, which requires `std` |
| `cvlr-soroban` | `faf7fb826f395cc0573a0ce674b7e4099cdf6f57` | Certora's `soroban-25.1.1` compatibility branch; its caret SDK requirement resolves to 25.3.2 |

The current `cvlr-soroban` main branch targets Soroban SDK 26 and is intentionally not used.

## Local setup

Python 3.9 or later, Java 21 or later, Rust, and the repository's `wasm32v1-none` target are required. Create an isolated Python environment and install the pinned CLI:

```sh
cd contracts/certora
python3 -m venv .venv
.venv/bin/python -m pip install -r requirements.txt
```

`run_certora.sh` uses Java from `PATH`, or an optional cached runtime at `.tools/java-21/Contents/Home`. Both `.venv` and `.tools` are ignored by Git. On Apple Silicon macOS, reproduce the pinned local Java cache with:

```sh
mkdir -p .tools
curl -L -C - --retry 3 -o .tools/temurin-jre-21.tar.gz https://github.com/adoptium/temurin21-binaries/releases/download/jdk-21.0.12.1%2B1/OpenJDK21U-jre_aarch64_mac_hotspot_21.0.12.1_1.tar.gz
tar -xzf .tools/temurin-jre-21.tar.gz -C .tools
mv .tools/jdk-21.0.12.1+1-jre .tools/java-21
rm .tools/temurin-jre-21.tar.gz
```

Set `CERTORAKEY` in the invoking shell before a cloud run. Do not commit or print the key.

If the prover is launched by a process that cannot inherit your terminal environment, store only the key in the ignored local file `.certora_key` and restrict its permissions:

```sh
printf '%s\n' "$CERTORAKEY" > .certora_key
chmod 600 .certora_key
```

`run_certora.sh` reads this file only when `CERTORAKEY` is otherwise unset.

Build the exact verification artifact without submitting it:

```sh
python3 certora_build.py --json --log
```

Build the conditional symbol-key artifact locally by passing the same extra feature that the conditional configuration supplies to the build script:

```sh
python3 certora_build.py --json --log --cargo_features certora-storage-symbols
```

Run Phase 0 through the wrapper, which selects the local tool cache when present and resolves each `build_script` path consistently:

```sh
./run_certora.sh phase0_smoke.conf --wait_for_results
./run_certora.sh phase0_conditional_storage_smoke.conf --wait_for_results
./run_certora.sh phase0_negative_control.conf --wait_for_results
./run_certora.sh phase0_failure_probe.conf --wait_for_results
```

A soundly compatible production-key toolchain should verify that two consecutive `get_total_supply` calls are equal, find a reachable nonzero supply, report the intentionally false negative control as `Violated`, and verify that an authorized zero-share join cannot return normally. The conditional configuration should also verify that all ten abstracted `DataKey` symbols are pairwise distinct. Certora does not permit `assert` and `satisfy` commands in the same rule, so reachability witnesses are separate satisfy-only rules. Any `Timeout` or `Unknown` is incomplete.

## Phase 0 conclusion

The build and cloud service integrations work, but the pinned SDK-25 verification stack is not yet sound enough for Comet's stateful proofs. In the [getter smoke report](https://prover.certora.com/output/6280446/60f1ebb1727b49e1a7b1761aa64d244f), Sunbeam finds two consecutive `get_total_supply` calls, with no intervening state-changing operation, that return `1` and `0`. The separate nonzero reachability rule is satisfiable. This behavior cannot occur under Soroban's storage semantics and demonstrates that the current verifier model does not preserve lookup identity for Comet's independently encoded `#[contracttype]` enum key. An earlier [direct seed/read diagnostic](https://prover.certora.com/output/6280446/30d35e9d18324188a26ab52eb6101d21) likewise allowed a seeded value of `1` to be read as `0`.

Do not treat a conditional result as closing the production-key smoke gate. A future adapter/prover combination must still verify the unchanged production encoding. In the meantime, storage-dependent analysis may proceed only within the scope of a validated verification abstraction.

The first abstraction increment is implemented by the `certora-storage-symbols` feature. It replaces the ten no-payload pool `DataKey` variants with distinct short symbols and therefore preserves equality and separation over that complete finite key set. The abstraction's injectivity, stable double read, and reachable nonzero read all verify in the [conditional smoke report](https://prover.certora.com/output/6280446/29c718811ff44b4082cab7029c309974). These results are conditional on treating the injective renaming as a faithful model of Soroban storage-key identity; they do not verify the production enum-vector serialization.

This increment does not abstract `DataKeyToken`. Its balance, nonce, state, and allowance variants contain addresses or nested payloads, so collapsing them to payload-free symbols would be unsound. Rules involving LP balances or allowances remain blocked until a separate modeled encoding preserves both the variant tag and address payloads and passes corresponding equality, separation, and read/write smoke checks. A workaround that merely assumes getter equality would restate the property and remains unacceptable.

## Failure-atomicity boundary

The SDK-25 CVLR adapter exposes rules as direct Rust calls but provides no catch/`try_` mechanism that resumes a rule after a Soroban abort. `phase0_rejected_join_cannot_return` can check that a zero-share join has no normal return under the verifier's abort semantics, but it cannot compare post-abort `EconomicState`. A passing result is not a proof that rollback occurred. Failure atomicity therefore remains outside the claimed Sunbeam scope until an adapter or host-level harness can expose both the failed result and rolled-back state without pruning the failure path.

## Phase 0 status

| Gate | Status | Evidence |
| --- | --- | --- |
| SDK/CVLR build compatibility | Passed locally | Verification-feature WASM builds with SDK 25.3.2, CVLR assertions 0.6.1, and the pinned SDK-25 adapter revision |
| Build-script/config ingestion | Passed locally | Certora CLI 8.19.1 accepts all four configuration files and collects the requested verification WASM and sources |
| Stateful getter semantics | Blocked | The [cloud smoke rule](https://prover.certora.com/output/6280446/60f1ebb1727b49e1a7b1761aa64d244f) is `Violated`: unchanged reads can return `1` then `0`; the nonzero reachability witness is satisfiable |
| Conditional no-payload `DataKey` semantics | Passed in cloud, conditional | The [conditional smoke report](https://prover.certora.com/output/6280446/29c718811ff44b4082cab7029c309974) verifies pairwise separation of all ten abstracted keys and a stable nonzero-reachable `get_total_supply` double read |
| Negative-control counterexample | Passed in cloud | The [negative control](https://prover.certora.com/output/6280446/65a471d803564fa89226a2cb4797b108) is `Violated` as expected |
| Rejected-call probe | Passed in cloud | The [rejected-call report](https://prover.certora.com/output/6280446/699a45726f7542a4be1a85ebf6ccabc2) verifies no normal return and finds the authorized pre-state witness; this does not prove rollback |
| Failure atomicity | Deferred | The pinned adapter cannot inspect state after an abort |
| Production build isolation | Passed locally | Normal WASM remains 34,435 bytes with SHA-256 `eeb751db34f657bb12f7dd59e584edba7d09437feca55fad1378c5896e566cba`, identical to the pre-scaffold build; verification WASM is built as a separate artifact |
| Existing regression suite | Passed locally | 31 contract tests, generated-constant check, and the complete Lean build pass |

## Build-isolation check

Build the production artifact with the normal feature set before and after changes, then compare its SHA-256 digest and byte length:

```sh
cargo build --release --package contracts --target wasm32v1-none
shasum -a 256 target/wasm32v1-none/release/contracts.wasm
wc -c target/wasm32v1-none/release/contracts.wasm
```

The verification build deliberately uses `RUSTFLAGS="-C strip=none"` and is not a deployment artifact. Rebuild without that environment variable before performing the production comparison.

## Diagnostics

- `certoraSorobanProver` missing: activate `.venv` or invoke its binary directly.
- Java startup error: install Java 21 or later and confirm `java --version`.
- Authentication error: export a valid `CERTORAKEY` without adding it to files or shell tracing.
- Build error: run `python3 certora_build.py --json --log` to expose Cargo output.
- `Timeout`/`Unknown`: keep the rule open; reduce symbolic state or split bounded cases rather than treating the result as verified.
- Unexpected production digest: cleanly rebuild without `--features certora` and without the verification `RUSTFLAGS`, then investigate before deployment.
