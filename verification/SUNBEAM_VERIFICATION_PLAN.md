# Certora Sunbeam verification plan

## Objective

Complement the existing Lean arithmetic proofs with implementation-level verification of the compiled Soroban contract. Lean remains the mathematical authority for the generalized-binomial, `c_pow` convergence, rounding-error, and fee-dominance results. Sunbeam should verify that the compiled WASM enforces the expected public guards and connects successful entrypoint results to the intended storage, LP-share, and underlying-token effects.

This work must not change production behavior. Verification-only dependencies, harnesses, mocks, and instrumentation should be excluded from normal contract builds.

## Assurance split

| Layer | Primary tool | Target guarantee |
| --- | --- | --- |
| Real and fixed-point mathematics | Lean | `c_pow` convergence and error bounds, directional rounding, fee dominance, and arithmetic representability |
| Compiled implementation | Sunbeam | Public guards, actual WASM control flow, return values, persistent-state changes, share accounting, and token-call arguments |
| Cross-tool bridge | Reviewed specification plus targeted Sunbeam rules | The implementation-level postconditions used by Sunbeam match the quantities and domains certified in Lean |

Sunbeam should directly prove an arithmetic property when tractable. If nonlinear arithmetic or the bounded `c_pow` loop must be summarized, the summary must expose the exact Lean-certified preconditions and postconditions rather than replacing the function with an unconstrained result. Every such summary is part of the documented trusted boundary.

## Scope

### Initial scope

- `init` and the initialized-pool state required by operation harnesses.
- Proportional liquidity: `join_pool` and `exit_pool`.
- Single-sided liquidity: `dep_tokn_amt_in_get_lp_tokns_out`, `dep_lp_tokn_amt_out_get_tokn_in`, `wdr_tokn_amt_in_get_lp_tokns_out`, and `wdr_tokn_amt_out_get_lp_tokns_in`.
- Swaps: `swap_exact_amount_in` and `swap_exact_amount_out`.
- Controller and freeze transitions needed to establish operation availability.
- Minimal invariant-preservation coverage for SEP-41 `transfer`, `transfer_from`, `burn`, and `burn_from`, without expanding into full SEP-41 functional verification.
- Pool storage, LP-share supply, selected-user share balances, underlying-token balance effects, and return values on successful calls.

### Deferred or excluded scope

- Full functional verification of the public SEP-41 allowance, transfer, burn, and metadata interface is excluded. Internal LP minting and burning remain in scope because liquidity safety depends on them. The four public methods that can change LP balances or `TotalShares` receive only the minimal preservation coverage required to close the shared accounting invariants.
- The factory contract is excluded from the first phase.
- Host, authentication, and standard token semantics are modeled dependencies, not proofs of the Soroban runtime or arbitrary external token implementations.
- Economic properties involving oracle values, front-running, price discovery, or profitability across multiple pools are excluded.
- Event contents and TTL-extension behavior are excluded from the initial economic-state proofs and may be verified separately.
- Resource bounds are tracked operationally but are not initially treated as functional correctness theorems.
- Failure atomicity is deferred. The pinned SDK-25 CVLR adapter provides no sound continuation after a Soroban abort, so it cannot compare pre- and post-abort `EconomicState`. A rule that merely proves the call cannot return normally is not a rollback proof.

## Proposed project structure

The exact layout should be confirmed during the compatibility spike, but the intended separation is:

```text
contracts/
  certora/
    README.md
    certora_build.py
    confs/
    mutations/
  src/
    certora_specs/
      mod.rs
      setup.rs
      initialization.rs
      proportional_liquidity.rs
      single_sided_liquidity.rs
      swaps.rs
      administration.rs
      invariants.rs
```

Spec modules and CVLR dependencies should be enabled only for the Sunbeam build. Configuration files should pin the CLI and verification-library versions and run one focused rule family at a time.

## Modeling policy

- Define one reusable `WellFormedPool` predicate before writing operation rules. It must cover initialization status; token-vector and record-map alignment; token uniqueness; record indices, weights, scalars, and balances; total weight and fee limits; record backing; nonnegative total shares and modeled LP balances; and the relationship between total supply and tracked LP balances needed by each rule.
- Prefer a nondeterministic initialized state constrained by `WellFormedPool` for operation rules. Separately prove that successful `init` establishes it and that every transition admitted by the verification scope preserves it.
- A global reachable-state claim requires preservation by every public method that can affect the claimed invariant. Full SEP-41 behavior remains out of scope, but `transfer`, `transfer_from`, `burn`, and `burn_from` must either have minimal preservation rules or explicit sound summaries. Without that closure, results must be described as operation-local and conditional on `WellFormedPool`.
- Cover each supported token count from 2 through 8 with separate bounded configurations if a symbolic vector length causes path explosion.
- Model a standards-compliant underlying token first. State every transfer, authorization, and rollback assumption explicitly.
- Use `actual_contract_token_balance >= recorded_pool_balance`, not equality, as the durable backing invariant because unsolicited token transfers can increase the actual balance without updating pool records.
- Define an `EconomicState` projection containing pool configuration, record balances, total shares, tracked LP balances, and modeled underlying-token balances. Unless a rule says otherwise, “unchanged state” means equality of this projection after removing the fields that the operation is intended to update. Expected TTL extensions and event emission are outside this projection.
- Avoid assumptions that restate the assertion being proved. Each assumption should have a named rationale and an owner: production guard, initialization invariant, host model, token model, or Lean-certified arithmetic fact.
- Demonstrate that Soroban aborts remain observable to the chosen Sunbeam/CVLR rule pattern before attempting failure atomicity. Every failure rule must contain both a witness that reaches the intended failure and a pre/post comparison that cannot be discharged by pruning the failed path.
- Treat every `Timeout` or `Unknown` result as incomplete, never as evidence that a rule holds.

## Direct and conditional verification modes

Use separate configurations so summaries cannot obscure what was checked:

- **Direct conformance mode:** Keep the production `c_pow` body enabled. Use verification-only observation hooks or ghosts to expose the stopping iteration and branch decisions without replacing the implementation. This mode owns claims about the compiled recurrence, the 46-iteration bound, correction branches, and mutations inside `c_pow`.
- **Conditional composition mode:** Permit a narrow Lean-backed arithmetic summary when proving public storage, share, transfer, and return-value composition. Results from this mode are conditional on the stated summary and do not independently verify the summarized function body.

Every report must identify which mode produced each result. A mutation inside a summarized body is meaningful only in direct conformance mode. If direct conformance times out or remains unknown, compiled-Rust-to-Lean arithmetic correspondence remains an open obligation even when conditional public-entrypoint rules verify.

## Work plan

### Phase 0: toolchain and compatibility spike

1. Confirm that the current `soroban-sdk` 25.3.2 contract builds with a pinned compatible `certora-cli`, CVLR, and `cvlr-soroban` version.
2. Add a verification-only build path that emits the WASM consumed by Sunbeam without affecting the normal release build.
3. Add one non-vacuous smoke rule over a simple getter and one deliberately failing rule to confirm counterexample reporting.
4. Add a failed-call capability rule that invokes a known-rejected public operation, proves that the failure path is reachable, and compares its pre/post `EconomicState`. If Sunbeam cannot observe the failed path soundly, move failure atomicity out of the claimed scope rather than relying on a vacuous rule.
5. Record local setup, cloud credentials, exact commands, expected report statuses, and common timeout diagnostics.
6. Compare a normal production build before and after scaffolding to confirm that verification instrumentation does not enter the deployed WASM.

The cloud compatibility spike produced counterexamples showing that the pinned SDK-25 verifier model can return different values from two consecutive `get_total_supply` calls with no intervening state-changing operation. The production-shaped smoke therefore remains an open compatibility gate. A separate `certora-storage-symbols` build provides an injective short-symbol encoding for the complete finite set of no-payload pool `DataKey` variants; pairwise key separation, stable repeated reads, and nonzero reachability verify in that conditional mode. A later write probe showed that even a raw short-symbol `set` followed immediately by `get` can violate round-trip semantics, so this abstraction supports only the validated read behavior and cannot support mutable pool-state proofs.

The `certora-lp-balance-ghost` build conditionally replaces the LP balance accessors with a one-watched-owner ghost projection. Equal and distinct address cases are reachable; repeated reads, matching writes, `receive_balance`/`spend_balance` composition, and distinct-owner isolation verify; and untracked reads remain nondeterministic rather than being assumed zero. This unblocks LP-balance reasoning only for an explicitly initialized watched owner and does not validate the production `DataKeyToken::Balance(Address)` encoding. Phase 1 still requires separately validated accessor-level ghosts for mutable pool metadata and any additional correlated owners or allowances. The negative control reports `Violated` as expected. The adapter can also observe that a rejected call has no normal return but cannot resume after the abort to inspect rolled-back storage, so failure atomicity remains deferred rather than relying on a vacuous claim.

### Phase 1: initialized-state foundation

Phase 1A establishes a conditional scalar-state foundation for controller presence/value, swap fee, total shares, and freeze status. The scalar accessors reproduce production defaults, round-trip arbitrary values, preserve field separation, remain independent of the one-account LP ghost, and compose with the actual `mint_shares` helper. A satisfy-only rule witnesses the complete successful scalar/LP path. These results verify in the [Phase 1A report](https://prover.certora.com/output/6280446/98f7271948624d41a25a5ce45209ddfd).

Phase 1B adds a conditional value-level model of the pool token vector and record map. Eight named slots cover the complete configured capacity without relying on symbolic Soroban collection handles, Rust arrays, symbolic indexing, or verifier loops. Initialization consumes the shared token-bound constants, and a verification-build compile-time assertion ties the maximum to the explicit ghost capacity. The rules check arbitrary value preservation, equal-address aliasing, absence of distinct unbound keys, every insertion and replacement slot, collection/scalar/LP isolation, token-to-record index alignment, and reachable two-token, equal/distinct-alias, eight-distinct-token, and full-capacity replacement states. The [maximum-capacity report](https://prover.certora.com/output/6280446/ad2492662c234ae199ace775c7d8bbdb) verifies every insertion slot and the maximum-size reachability check; the [aliasing report](https://prover.certora.com/output/6280446/612e830454984d058072af65d7d46373) and [supplemental report](https://prover.certora.com/output/6280446/a0fb382b557c496982c76786a0ec4e53) verify equal-key replacement, missing-key behavior, vector bounds, and the aliasing witness; the [replacement-branch report](https://prover.certora.com/output/6280446/b2079e8161974852bd8dd6431ac14156) verifies all eight constant-index replacement rules; and the strengthened [full-capacity witness](https://prover.certora.com/output/6280446/3e6b9073bb324ebe8ae8fa4a123c71e2) verifies that both eight-slot collections, every populated getter, and the slot-seven replacement return normally. The constant-case split follows the same discipline used by mature Certora suites: bound finite structures, isolate expensive paths by operation or case, and validate proof summaries and reachability separately. Record mutations take effect immediately in the ghost, which is equivalent to the source read-modify-write sequence only for successful operations; failure rollback remains outside scope. The full `init` proof remains open pending initialization routing, LP metadata, token-call, and authorization models.

Prove that a successful `init` establishes the state used by later rules:

- Initialization is single-use and requires controller authorization.
- Token count is in `[2, 8]`; token addresses are unique; vectors are aligned.
- Each record preserves its token, weight, balance, scalar, and index association.
- Weights and fees satisfy the configured limits and total weight equals `STROOP`.
- Each initial underlying transfer uses the configured balance and leaves the pool sufficiently backed.
- `TotalShares == INIT_POOL_SUPPLY` and the controller receives exactly that LP balance.
- Controller, token vector, record map, fee, and LP metadata are stored consistently, and an absent freeze key reads as `false`.
- Rejected-initialization rollback is not claimed until a future adapter or host-level harness exposes post-abort state soundly.

### Phase 2: proportional liquidity first

These paths avoid `c_pow` and should establish the first end-to-end liquidity guarantees.

For `join_pool`, prove on every successful call:

- The caller authorized the operation and the pool was not frozen.
- The LP supply and caller LP balance increase by exactly `pool_amount_out`.
- Each record balance and corresponding underlying-token transfer increase by exactly the computed charge; unrelated `EconomicState` fields are unchanged.
- Every charge respects its user maximum and is positive.
- For pre-state record balance `B`, pre-state supply `S`, minted shares `dS`, and token charge `dB`, `dB * S >= B * dS` in mathematical integer arithmetic.

For `exit_pool`, prove on every successful call:

- The caller authorized the operation; exit remains available while frozen.
- The LP supply and caller LP balance decrease by exactly `pool_amount_in`.
- Each record balance and corresponding underlying-token balance decrease by exactly the transferred output; unrelated `EconomicState` fields are unchanged.
- Every output respects its user minimum, is positive, and does not exceed either recorded or actual backing.
- For pre-state record balance `B`, pre-state supply `S`, burned shares `dS`, and token output `dB`, `dB * S <= B * dS` in mathematical integer arithmetic.

### Phase 3: compiled `c_pow` bridge

1. In direct conformance mode, isolate `c_pow` in a focused harness over the configured base, exponent, precision, and iteration domains while keeping the production body enabled.
2. Add observation-only instrumentation for the stopping iteration and correction branch, and confirm that it is absent from normal production WASM.
3. Attempt to prove directly that supported operating-band executions reach the stopping threshold by iteration 46 and therefore cannot exhaust the 50-iteration loop.
4. Check that the compiled integer/fractional exponent split and each correction branch agree with the source structure covered by Lean.
5. Define the cross-tool boundary explicitly. Continuous real exponentiation is not a compiled contract operation, so any Lean-certified relation involving the continuous fee-free ideal must enter Sunbeam as a named assumed postcondition unless an independent SMT encoding is supplied. Cross-multiply rational scale factors where possible, but do not describe that transformation as eliminating the real-power assumption.
6. In conditional composition mode, introduce the narrowest useful summary and record its exact function boundary, Lean theorem, constants, domain, and postcondition. Mutation-test summary preconditions and call sites there, but reserve mutations of the summarized body for direct conformance mode.

The 46-iteration and adverse-error results should not be claimed as independently verified by Sunbeam when they are supplied through a Lean-backed summary. If the direct rules do not verify, the final report must say that Sunbeam verified only the public composition conditional on the Lean-certified arithmetic contract.

### Phase 4: single-sided liquidity

For all four entrypoints, prove common implementation properties:

- Freeze behavior: deposits are rejected while frozen and withdrawals remain available.
- The selected token is bound, the amount is positive, and the configured maximum-ratio and user-limit guards hold.
- Only the selected token record changes.
- Deposit record balance and actual token receipt increase by exactly the charged token amount.
- Withdrawal record balance and actual token transfer decrease by exactly the returned token amount without exceeding backing.
- `TotalShares` and the caller's LP balance change by exactly the minted or burned amount.
- The function return value agrees with the token or LP delta advertised by its public interface.

Then connect each successful operation to the corresponding Lean-certified direction:

| Entrypoint | Target postcondition relative to the continuous fee-free ideal |
| --- | --- |
| `dep_tokn_amt_in_get_lp_tokns_out` | Computed LP output is strictly lower |
| `dep_lp_tokn_amt_out_get_tokn_in` | Computed token input is strictly higher |
| `wdr_tokn_amt_in_get_lp_tokns_out` | Computed token output is strictly lower |
| `wdr_tokn_amt_out_get_lp_tokns_in` | Computed LP input is strictly higher |

The bridge must retain the precise operation-specific adverse-error budgets and show that the configured fee advantage dominates them; a generic unconstrained `c_pow` summary is insufficient.

### Phase 5: swaps

For both swap directions, prove:

- Authorization, freeze, distinct-token, positivity, bound-token, maximum-ratio, slippage, and maximum-price guards.
- The input record and actual pool token balance increase by the charged input; the output record and actual pool token balance decrease by the transferred output.
- No unrelated record, LP balance, or total supply changes.
- Returned input/output and post-swap spot price agree with the state transition.
- The post-swap spot price is not below the pre-swap price and respects the caller's maximum.
- The Lean-certified fee-dominance postcondition reaches the compiled public result for each successful direction.

### Phase 6: persistent invariants and administration

- Every recorded token remains backed: actual contract token balance is at least its record balance.
- Token addresses, weights, scalars, and indices remain unchanged after initialization.
- Record balances, total shares, and modeled LP balances remain nonnegative.
- Minting and burning change `TotalShares` and LP balances by the same amount; ordinary pool operations cannot create unaccounted shares.
- `transfer` and `transfer_from` preserve `TotalShares` and the tracked aggregate LP balance while changing only the intended account balances and allowance where applicable.
- `burn` and `burn_from` reduce `TotalShares` and the source LP balance by the same amount while preserving the remaining `WellFormedPool` obligations.
- Only the current controller can change the controller or freeze status.
- Controller changes preserve all other `EconomicState` fields.
- Freeze changes preserve all other `EconomicState` fields and only change operation availability within that projection.
- Simple pool getters return the corresponding stored value without modifying `EconomicState`; expected TTL extensions remain outside the projection.

## Targeted validation matrix

| Validation | Required evidence |
| --- | --- |
| Build isolation | Normal release WASM contains no CVLR/spec instrumentation and has no executable-code change attributable to Sunbeam scaffolding |
| Reachability | Every passing rule also passes non-vacuity/satisfiability checks for its successful path |
| Negative controls | Deliberately false smoke rules produce understandable counterexamples |
| Rejected-call capability | A known-rejected call has a reachable pre-state witness and cannot return normally under the verifier's abort semantics |
| Failure atomicity (deferred) | A future adapter or host-level harness exposes the failed result and rolled-back `EconomicState` without pruning the failure path |
| Rule result | Every required rule reports `Verified`; `Violated`, `Timeout`, and `Unknown` remain open work |
| Assumption audit | Every assumption and summary is listed with its justification and affected rules |
| Transition closure | `WellFormedPool` is established by `init` and preserved by every in-scope method plus the four minimal SEP-41 transitions, or claims are explicitly operation-local |
| Token-count coverage | Rules cover each supported size 2 through 8, or document a sound symbolic proof of the bounded loop |
| Mutation strength | Relevant mutations are rejected by at least one intended rule |
| Lean bridge | Each imported arithmetic postcondition names the exact Lean theorem, constants, domain, and inequality used |
| Regression | Existing Rust tests, Lean build, generated-constant check, and Sunbeam rule families all pass |
| Reproducibility | Pinned versions, configuration files, report links, and invocation commands are committed |

## Initial mutation set

- Change proportional join ceiling rounding to floor rounding.
- Change proportional exit floor rounding to ceiling rounding.
- Skip or mis-size an underlying-token transfer.
- Skip an LP mint or burn, or update `TotalShares` by the wrong amount.
- Update the returned amount without making the corresponding record change.
- Remove a user maximum/minimum, maximum-ratio, same-token, or balance guard.
- Allow a deposit or swap while frozen, or block an exit while frozen.
- Remove controller or user authorization.
- Remove the fee adjustment or reverse a `c_pow` correction direction; run body mutations in direct conformance mode.
- Change the `c_pow` iteration cap, precision, exponent split, or configured constant; require the direct conformance rules to reject the mutation.

## Completion criteria

The first meaningful milestone is complete when successful proportional join and exit executions are verified end to end against the compiled WASM, including authorization, freeze behavior, exact storage/share/token deltas, backing, user limits, pool-favoring cross-multiplied rounding inequalities, and preservation of a named `WellFormedPool` predicate over the declared transition scope. The second milestone adds the four single-sided liquidity paths with explicit Lean-backed fee-dominance postconditions and labels those results conditional unless direct conformance also verifies the compiled arithmetic body. Swaps, broader persistent invariants, and administration follow without weakening assumptions introduced by the liquidity milestones. Failure atomicity remains a separate future milestone that requires sound post-abort observation support.

The final report must distinguish properties proved directly over WASM from properties obtained by composing WASM verification with a Lean-certified summary.
