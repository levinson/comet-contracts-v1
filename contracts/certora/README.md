# Comet Sunbeam verification

This directory contains verification-only Certora Sunbeam configuration. Normal contract builds do not enable the `certora` feature and therefore exclude the rules and CVLR dependencies from deployed WASM. Conditional features provide an injective short-symbol `DataKey` encoding, a one-account LP-balance ghost, a scalar pool-state ghost, and an explicit bounded-slot model of the pool token vector and record map. None are deployment features.

## Pinned compatibility set

| Component | Pin | Reason |
| --- | --- | --- |
| Rust | `1.92.0` | Repository `rust-toolchain.toml` |
| Java | Temurin JRE `21.0.12.1+1` | Local Apple Silicon cache used for the compatibility spike |
| Soroban SDK | `25.3.2` | Workspace dependency |
| Certora CLI | `8.19.1` | Python dependency in `requirements.txt` |
| CVLR assertions | `0.6.1` | Exact `no_std` optional dependency; the umbrella `cvlr` crate includes `cvlr-spec`, which requires `std` |
| CVLR nondeterminism | `0.6.1` | Exact `no_std` optional dependency used by the LP ghost's unconstrained fallback |
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

Build the conditional one-account LP-balance ghost artifact similarly:

```sh
python3 certora_build.py --json --log --cargo_features certora-lp-balance-ghost,certora-storage-symbols
```

Build the Phase 1 scalar/LP foundation artifact:

```sh
python3 certora_build.py --json --log --cargo_features certora-pool-scalar-ghost,certora-lp-balance-ghost
```

Build the Phase 1 collection/scalar/LP foundation artifact:

```sh
python3 certora_build.py --json --log --cargo_features certora-pool-collections-ghost,certora-pool-scalar-ghost,certora-lp-balance-ghost
```

Run the verification configurations through the wrapper, which selects the local tool cache when present and resolves each `build_script` path consistently:

```sh
./run_certora.sh phase0_smoke.conf --wait_for_results
./run_certora.sh phase0_conditional_storage_smoke.conf --wait_for_results
./run_certora.sh phase0_conditional_storage_write_probe.conf --wait_for_results
./run_certora.sh phase0_conditional_lp_balance_smoke.conf --wait_for_results
./run_certora.sh phase0_negative_control.conf --wait_for_results
./run_certora.sh phase0_failure_probe.conf --wait_for_results
./run_certora.sh phase1_scalar_state_smoke.conf --wait_for_results
./run_certora.sh phase1_collection_state_smoke.conf --wait_for_results
```

A soundly compatible production-key toolchain should verify that two consecutive `get_total_supply` calls are equal, find a reachable nonzero supply, round-trip a written supply, report the intentionally false negative control as `Violated`, and verify that an authorized zero-share join cannot return normally. The conditional symbol-key configuration should verify that all ten abstracted `DataKey` symbols are pairwise distinct. The storage-write probe is currently expected to be `Violated`, while every rule in the LP-balance ghost configuration is expected to verify. Certora does not permit `assert` and `satisfy` commands in the same rule, so reachability witnesses are separate satisfy-only rules. Any `Timeout` or `Unknown` is incomplete.

## Phase 0 conclusion

The build and cloud service integrations work, but the pinned SDK-25 verification stack is not yet sound enough for Comet's stateful proofs. In the original [getter smoke report](https://prover.certora.com/output/6280446/60f1ebb1727b49e1a7b1761aa64d244f), Sunbeam finds two consecutive `get_total_supply` calls, with no intervening state-changing operation, that return `1` and `0`. The expanded [production-key smoke report](https://prover.certora.com/output/6280446/9bfef3b8d0cb4dbb9dfac5319e093107) independently violates both that stable-read rule and the unconditional `put_total_shares`/`get_total_shares` round trip, while the separate nonzero reachability rule remains satisfiable. This behavior cannot occur under Soroban's storage semantics and demonstrates that the current verifier model does not preserve lookup identity for Comet's independently encoded `#[contracttype]` enum key. An earlier [direct seed/read diagnostic](https://prover.certora.com/output/6280446/30d35e9d18324188a26ab52eb6101d21) likewise allowed a seeded value of `1` to be read as `0`.

Do not treat a conditional result as closing the production-key smoke gate. A future adapter/prover combination must still verify the unchanged production encoding. In the meantime, storage-dependent analysis may proceed only within the scope of a validated verification abstraction.

The first abstraction increment is implemented by the `certora-storage-symbols` feature. It replaces the ten no-payload pool `DataKey` variants with distinct short symbols and therefore preserves equality and separation over that complete finite key set. The abstraction's injectivity, stable double read, and reachable nonzero read all verify in the [conditional read smoke report](https://prover.certora.com/output/6280446/29c718811ff44b4082cab7029c309974). These results are conditional on treating the injective renaming as a faithful model of Soroban storage-key identity; they do not verify the production enum-vector serialization. More importantly, the [conditional write probe](https://prover.certora.com/output/6280446/7b120b042b4d43f4a362d47c85120a4a) is `Violated` even for a raw short-symbol `set` immediately followed by `get`, without a TTL call. The current host model is therefore unsuitable for mutable pool metadata even after key renaming.

The second increment, `certora-lp-balance-ghost`, follows the one-entry ghost-map pattern used by prior Certora Soroban projects. It replaces only `read_balance` and `write_balance` in the verification build with a WASM-resident projection containing one explicitly selected `Address` and its `i128` balance. Writes update only a semantically equal address; reads of every other address are nondeterministic rather than assumed to be zero. The [LP-balance ghost report](https://prover.certora.com/output/6280446/1b0f2502f97d411abcf048e87204b84e) verifies repeated reads, direct writes, composition through `receive_balance` and `spend_balance`, equal-address aliasing, distinct-address isolation, reachability of equal and distinct cases, an unconstrained untracked balance, and survival across an unrelated pool-storage write.

This ghost result is an accessor-level conditional proof, not validation of `DataKeyToken::Balance(Address)` serialization or SDK-25 host storage. It is sound only for rules whose claimed LP state is confined to the explicitly initialized watched owner; a rule may not claim a concrete value for an untracked owner after writing it. Allowances, nonce/state entries, multiple correlated LP owners, and aggregate-supply relationships require additional projections and validation. The remaining mutable pool state—especially token vectors, records, and LP metadata—also requires accessor-level ghost summaries before Phase 1 can establish fully initialized state. A workaround that merely assumes getter equality would restate the property and remains unacceptable.

## Phase 1A scalar-state foundation

The `certora-pool-scalar-ghost` feature conditionally replaces the controller, swap-fee, total-shares, and freeze accessors with a WASM-resident state projection. It retains controller presence separately from its value so the real single-initialization guard can distinguish an uninitialized pool. Missing fee and total-shares values read as zero, while a missing freeze flag reads as false, matching the production accessors.

The [Phase 1A report](https://prover.certora.com/output/6280446/98f7271948624d41a25a5ce45209ddfd) verifies the default state, arbitrary-value round trips, field isolation, independence from the one-account LP ghost, and equal supply/owner changes through the actual `mint_shares` helper. A separate satisfy-only rule witnesses a normal return through the combined controller, fee, freeze, supply, LP-balance, and mint path.

This is not yet a proof of the public `init` entrypoint. Token vectors, record maps, LP metadata, token decimals and transfers, authorization, and the complete initialization postcondition still require independently validated models and rules.

## Phase 1B bounded collection foundation

The `certora-pool-collections-ghost` feature conditionally routes pool-operation token-vector and record-map access through a value-level WASM ghost with eight explicit slots, matching the contract's configured maximum token count. Production initialization consumes the shared `MIN_BOUND_TOKENS` and `MAX_BOUND_TOKENS` constants, and a verification-build compile-time assertion rejects any maximum that differs from the explicit ghost capacity. The adapter retains initialization state, length, insertion order, address-keyed lookup, record replacement, and every `Record` field. It uses named scalar slots rather than Soroban object handles, Rust arrays, symbolic indexing, or verifier loops.

That representation follows the pattern used by existing Soroban verification work: Certora's [reflector example](https://github.com/Certora/reflector-subscription-contract/blob/51944577dc4536e9cf9711db6e125fe1e2254054/src/certora_specs/mod.rs) uses raw one-key ghost storage, its [token summary](https://github.com/Certora/reflector-subscription-contract/blob/51944577dc4536e9cf9711db6e125fe1e2254054/src/certora_specs/token.rs) replaces external token behavior in verification builds, the pinned adapter provides a [`mock_client` macro](https://github.com/Certora/cvlr-soroban/blob/faf7fb826f395cc0573a0ce674b7e4099cdf6f57/cvlr-soroban-derive/src/mock_client.rs), and prior Blend verification submissions conditionally route production storage access through [raw ghost maps](https://github.com/code-423n4/2025-02-blend-fv/blob/fc843bcc188cd796212c6ad7d9a148cad490da04/Example_Submissions/backstop-jraynaldi3/src/certora_specs/summaries/storage.rs). Comet's model expands the raw-state approach into a fully explicit bounded collection so it does not depend on the verifier preserving symbolic Soroban `Vec` or `Map` handles. Mature EVM suites use the same broader discipline: Aave [maintains aggregate ghost state with storage hooks and proves its consistency invariant](https://github.com/aave/aave-v3-core/blob/master/certora/specs/AToken.spec), while Morpho Midnight [bounds loops, verifies one entry point at a time, and justifies difficult summaries with separate proofs](https://github.com/morpho-org/midnight/blob/main/certora/README.md).

Two rejected diagnostics make that choice testable rather than stylistic. Storing `Option<Vec<Address>>` and `Option<Map<Address, Record>>` directly failed to preserve symbolic contents in the [object-handle diagnostic](https://prover.certora.com/output/6280446/84421322063d4652a8001374b990bcc3). Raw Rust arrays and loops then failed scalarization and loop unwinding in the [array diagnostic](https://prover.certora.com/output/6280446/2117c4469ee14a048dd328f9c5f8156f). The explicit-slot model verifies arbitrary two-token round trips, equal-address aliasing, absence of a distinct unbound key, token/record and scalar/LP isolation, record-index alignment, every record-replacement branch, and successful-state reachability. Separate satisfy-only rules establish that the equal/distinct aliasing condition, eight pairwise-distinct addresses, and the full-capacity slot-seven replacement are reachable. The [maximum-capacity report](https://prover.certora.com/output/6280446/ad2492662c234ae199ace775c7d8bbdb) exercises all eight token and record slots; the [aliasing report](https://prover.certora.com/output/6280446/612e830454984d058072af65d7d46373) and [supplemental round-trip/reachability report](https://prover.certora.com/output/6280446/a0fb382b557c496982c76786a0ec4e53) close the additional key-identity and non-vacuity checks; the [replacement-branch report](https://prover.certora.com/output/6280446/b2079e8161974852bd8dd6431ac14156) verifies all eight constant-index replacement rules; and the strengthened [full-capacity witness](https://prover.certora.com/output/6280446/3e6b9073bb324ebe8ae8fa4a123c71e2) verifies that both eight-slot collections, every populated getter, and the slot-seven replacement return normally.

`CertoraPoolRecordMap::set` updates the ghost immediately and its write adapter is a no-op. This has the same final state as the production read-modify-write pattern on successful operations, which is the current proof scope. It does not model a discarded local map or post-abort rollback. The model also does not validate production collection serialization or host storage, and `init` is not yet routed through it. A complete Phase 1 result still requires LP metadata, token clients, authorization, and a source-shaped initialization rule.

## Failure-atomicity boundary

The SDK-25 CVLR adapter exposes rules as direct Rust calls but provides no catch/`try_` mechanism that resumes a rule after a Soroban abort. `phase0_rejected_join_cannot_return` can check that a zero-share join has no normal return under the verifier's abort semantics, but it cannot compare post-abort `EconomicState`. A passing result is not a proof that rollback occurred. Failure atomicity therefore remains outside the claimed Sunbeam scope until an adapter or host-level harness can expose both the failed result and rolled-back state without pruning the failure path.

## Phase 0 status

| Gate | Status | Evidence |
| --- | --- | --- |
| SDK/CVLR build compatibility | Passed locally | Verification-feature WASM builds with SDK 25.3.2, CVLR assertions 0.6.1, and the pinned SDK-25 adapter revision |
| Build-script/config ingestion | Passed locally | Certora CLI 8.19.1 accepts the direct and conditional configurations and collects the requested verification WASM and sources |
| Production host-storage semantics | Blocked | The [expanded direct smoke report](https://prover.certora.com/output/6280446/9bfef3b8d0cb4dbb9dfac5319e093107) violates both stable repeated reads and the unconditional accessor-level write/read round trip; the nonzero reachability witness is satisfiable |
| Conditional no-payload `DataKey` read semantics | Passed in cloud, conditional | The [conditional read smoke report](https://prover.certora.com/output/6280446/29c718811ff44b4082cab7029c309974) verifies pairwise separation of all ten abstracted keys and a stable nonzero-reachable `get_total_supply` double read |
| Conditional host-storage write semantics | Blocked | The [write probe](https://prover.certora.com/output/6280446/7b120b042b4d43f4a362d47c85120a4a) violates both the metadata-accessor and raw short-symbol round trips |
| Conditional one-account LP balance | Passed in cloud, conditional | All nine aliasing, isolation, reachability, helper-composition, and unconstrained-fallback rules verify in the [ghost report](https://prover.certora.com/output/6280446/1b0f2502f97d411abcf048e87204b84e) |
| Phase 1 scalar-state foundation | Passed in cloud, conditional | The [Phase 1A report](https://prover.certora.com/output/6280446/98f7271948624d41a25a5ce45209ddfd) verifies five scalar/LP assertion rules and one successful-path witness |
| Phase 1 bounded collection foundation | Passed in cloud, conditional | The Phase 1B reports cover capacity/configuration coupling, arbitrary values, aliasing, missing keys, all eight insertion and replacement slots, isolation, alignment, and non-vacuous witnesses without symbolic Soroban collection handles |
| Full Phase 1 initialization proof | In progress | Initialization routing, LP metadata, token calls, authorization, and the public-entrypoint composition remain open |
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
