# Comet Pool Public Entrypoint Proof Coverage

This table inventories every public entrypoint implemented by `contracts/src/c_pool/comet.rs`. “Covered” means Lean proves the stated property from a successful executable, source-shaped model of the relevant arithmetic or configuration path. The models are handwritten rather than extracted from Rust. Unless a row says otherwise, authorization, storage operations, external token calls, transfers, share minting or burning, TTL behavior, and event emission remain outside the machine-checked boundary.

| Public entrypoint | Proof status | Established machine-checked property | Principal Lean result |
| --- | --- | --- | --- |
| `init` | Covered: configuration model | Successful execution enforces the uninitialized, token-count, vector-length, fee, duplicate-token, weight, balance, decimal, checked weight-accumulation, and exact-total guards. Records preserve token, weight, balance, queried-decimal, and index alignment; every scalar is positive and at most `BONE`; the configured initial LP mint amount is positive. The resulting persistent supply is not modeled. | `initializationExecution_establishes_invariants` |
| `join_pool` | Covered: arithmetic model | Successful full-list execution reconstructs the shared ceiling ratio and every token upscale, ceiling multiplication, ceiling downscale, positive/max-input guard, and checked balance addition. Every required token deposit is at least its ideal proportional share, so rounding cannot undercharge the pool. | `joinPoolExecution_every_token_cannot_undercharge` |
| `exit_pool` | Covered: arithmetic model | Successful full-list execution reconstructs the shared floor ratio and every token upscale, floor multiplication, floor downscale, positive/min-output/available-balance guard, and balance update. Every token withdrawal is at most its ideal proportional share, so rounding cannot overpay the user. | `exitPoolExecution_every_token_cannot_overpay` |
| `swap_exact_amount_in` | Covered: arithmetic and approximation model | Successful source-shaped execution reconstructs checked scaling, fee adjustment, ratio/exponent rounding, every `c_pow` control-flow case, final output floors, and relevant public arithmetic guards. A signed recurrence proof establishes that pool-adverse approximation error is strictly below `17/800 = 2.125%` of the minimum fee’s spot-normalized value. | `calc_token_out_given_token_in_execution_adverse_error_lt_precise_fee_share` |
| `swap_exact_amount_out` | Covered: arithmetic and approximation model | Successful source-shaped execution reconstructs checked scaling, ratio/exponent ceilings, upper-rounded integer power, every `c_pow` correction branch, fee division, input ceilings, and relevant public arithmetic guards. Pool-adverse approximation error is strictly below `4501/100000 = 4.501%` of the adjusted minimum fee’s spot-normalized value. | `calc_token_in_given_token_out_execution_adverse_error_lt_precise_fee_share` |
| `dep_tokn_amt_in_get_lp_tokns_out` | Covered: arithmetic and approximation model | Successful exact-token-input single-sided deposit execution reconstructs fee-adjusted input and balance-ratio floors, direct-weight `c_pow`, new-supply floor, LP-token downscale, and public limit guards. Pool-adverse approximation error is strictly below `1223/100000 = 1.223%` of the weighted minimum fee’s normalized value. | `calc_lp_token_amount_given_token_deposits_in_execution_adverse_error_lt_precise_fee_share` |
| `dep_lp_tokn_amt_out_get_tokn_in` | Covered: arithmetic and approximation model | Successful exact-LP-output single-sided deposit execution reconstructs supply-ratio and reciprocal-weight ceilings, every upper-directed `c_pow` branch, new-balance and fee ceilings, token downscale ceiling, and `MAX_IN_RATIO` guard. Pool-adverse approximation error is strictly below `1107/100000 = 1.107%` of the adjusted weighted minimum fee’s normalized value. | `calc_token_deposits_in_given_lp_token_amount_execution_adverse_error_lt_precise_fee_share` |
| `wdr_tokn_amt_in_get_lp_tokns_out` | Covered: arithmetic and approximation model | Successful exact-LP-input single-sided withdrawal execution reconstructs supply-ratio ceiling, reciprocal-weight floor, every upper-directed `c_pow` branch, new-balance ceiling, fee and token floors, and balance-cap guards. Pool-adverse approximation error is strictly below `3001/100000 = 3.001%` of the weighted minimum fee’s normalized value; successful low-base cases are proved pool-favoring separately. | `calc_token_withdrawal_amount_given_lp_token_amount_execution_adverse_error_lt_precise_fee_share` |
| `wdr_tokn_amt_out_get_lp_tokns_in` | Covered: arithmetic and approximation model | Successful exact-token-output single-sided withdrawal execution reconstructs the output guard, fee ceiling, remaining-balance floor, direct-weight `c_pow`, new-supply floor, LP-token ceiling, and public limit guards. Pool-adverse approximation error is strictly below 5% of the adjusted weighted minimum fee’s normalized value; successful low-base cases are proved pool-favoring separately. | `calc_lp_token_amount_given_token_withdrawal_amount_execution_adverse_error_lt_five_percent_min_fee` |
| `set_controller` | Not covered | No machine-checked authorization or controller-storage transition theorem. | — |
| `set_freeze_status` | Not covered | No machine-checked authorization or freeze-state transition theorem. | — |
| `get_total_supply` | Not covered | No source-shaped theorem connecting the persistent `TotalShares` value to the public return value. The initialization proof covers the configured mint amount, not stored total supply. | — |
| `get_controller` | Not covered | No source-shaped storage getter theorem. | — |
| `get_tokens` | Not covered | No source-shaped storage getter theorem. | — |
| `get_balance` | Not covered | No source-shaped theorem connecting the selected stored record balance to the public return value. | — |
| `get_normalized_weight` | Not covered | No source-shaped theorem connecting the selected stored record weight to the public return value. Initialization does prove the bounds of every modeled initial record weight. | — |
| `get_spot_price` | Covered: arithmetic model | Successful positive-denominator execution reconstructs all four checked i128 floor divisions, proves representability and a two-sided error envelope around the continuous weighted spot price, proves the fee-adjusted result is not below the zero-fee result, proves fee monotonicity, and proves the computed price cannot decrease after the modeled swap balance update. Record lookup is not modeled. | `calc_spot_price_execution_error_bounds`; `successful_get_spot_price_not_below_sans_fee`; `successful_spot_price_is_monotone_in_fee`; `successful_spot_price_does_not_decrease_after_swap_balance_update` |
| `get_swap_fee` | Not covered | No source-shaped storage getter theorem. Initialization does prove that the modeled initially stored fee satisfies `MIN_FEE ≤ fee ≤ MAX_FEE`. | — |
| `get_spot_price_sans_fee` | Covered: arithmetic model | Successful positive-denominator execution inherits the spot-price representability and error envelope; setting the fee to zero makes the final fee division an identity. Record lookup is not modeled. | `calc_spot_price_execution_error_bounds`; `SuccessfulSpotPriceRun.sans_fee_returns_ratio` |
| SEP-41 `allowance` | Intentionally out of scope | No allowance-storage or expiry proof is planned in this project. | — |
| SEP-41 `approve` | Intentionally out of scope | No authorization, amount-validation, allowance-write, expiry, or event proof is planned in this project. | — |
| SEP-41 `balance` | Intentionally out of scope | No LP-token balance-storage getter proof is planned in this project. | — |
| SEP-41 `transfer` | Intentionally out of scope | No LP-token balance transition, conservation, authorization, or event proof is planned in this project. | — |
| SEP-41 `transfer_from` | Intentionally out of scope | No allowance-spend, balance transition, authorization, or event proof is planned in this project. | — |
| SEP-41 `burn` | Intentionally out of scope | No LP-token balance and total-supply reduction proof is planned in this project. | — |
| SEP-41 `burn_from` | Intentionally out of scope | No allowance-spend, LP-token balance, or total-supply reduction proof is planned in this project. | — |
| SEP-41 `decimals` | Intentionally out of scope | No metadata-storage getter proof is planned in this project. The initialization model records the configured value `7` without modeling its storage write or getter. | — |
| SEP-41 `name` | Intentionally out of scope | No metadata-storage getter proof is planned in this project. | — |
| SEP-41 `symbol` | Intentionally out of scope | No metadata-storage getter proof is planned in this project. | — |

## Shared proof foundation

The `c_pow` entrypoint results above share machine-checked generalized-binomial direction proofs, a concrete three-floor recurrence-error budget, upper-rounded exponentiation-by-squaring refinements, configured exponent limits, and convergence within 46 iterations throughout the supported `[0.5, 1.6]` operating band. Entrypoint-specific low-base cases that can fall outside that band are handled separately by pool-favoring theorems or an explicit bounded execution trace.

The checked i128 and signed-I256 refinements are imported from the pinned `soroban-fixed-point-math` verification dependency. The generated Lean constants bind the proofs to the production Rust configuration, including ratios, weights, fees, precision, iteration and exponent limits, minimum balance, and configured initial mint amount.

## Coverage summary

Of the 19 pool-specific public entrypoints, 11 have source-shaped configuration or arithmetic proofs and 8 administrative or simple storage entrypoints remain unproved. All 10 SEP-41 methods are intentionally out of scope. No current theorem claims fully extracted Rust correspondence or end-to-end contract-state, authorization, external-call, transfer, mint/burn, TTL, or event correctness.

## Appendix: Terminology

### Error direction

**Ideal value.** The result of the corresponding continuous real-arithmetic formula, before fixed-point truncation, directional rounding, or finite-series approximation. It is the mathematical reference used by the error theorems, not an independently executable contract path.

**Computed value.** The result returned by the successful source-shaped Lean model of the contract arithmetic. A theorem about a computed value assumes that the model returns `some`, so every modeled checked operation and guard succeeded.

**Approximation error.** The difference between the computed and ideal values that can arise from the finite `c_pow` series and its fixed-point recurrence. Entrypoint theorems compare the full source-shaped arithmetic path, so their bounds also account for surrounding floors and ceilings; those operations are separately shown to round in the pool's favor where claimed.

**Pool-adverse approximation error.** The positive part of the computed-versus-ideal gap in the direction that benefits the caller at the pool's expense. For a fixed-input operation, this is excess computed output, `max(computedOutput - idealOutput, 0)`. For a fixed-output operation, this is deficient computed input, `max(idealInput - computedInput, 0)`. Thus a join is adverse if it requires too little token input, while an exit is adverse if it returns too much token output. A zero adverse error means the approximation is exact or pool-favoring; it does not mean the absolute approximation error is zero.

**Pool-favoring error.** Error in the opposite direction: the caller receives no more than the ideal output or supplies no less than the ideal input. Pool-favoring error may still be nonzero as an absolute numerical error.

**Absolute error.** The unsigned magnitude `|computed - ideal|`, irrespective of who benefits. The percentage bounds in this verification concern only pool-adverse error unless a theorem explicitly says otherwise.

### Fee comparison scale

**Minimum fee rate.** The contract configuration floor `MIN_FEE / STROOP = 1 / 1,000,000`, or `10^-6` of the relevant nominal amount. This is the pool's minimum swap-fee rate, not the Soroban transaction fee paid for ledger execution.

**Nominal ratio.** The operation's unadjusted amount divided by its relevant reserve balance or LP-token supply. It is the dimensionless first-order movement used when expressing the fee and approximation error on a common scale.

**Spot-normalized.** Converted into the same output, input, or LP-token unit as the error using the invariant's local first-order slope at the pre-operation state. This is a mathematical normalization; it does not use an oracle price.

**Minimum fee's spot-normalized value.** A conservative comparison scale obtained by applying the minimum fee rate to the nominal operation size and converting that amount into the theorem's error unit at the invariant's local spot slope. For example, the exact-input swap scale in output-token units is `MIN_FEE_RATE * outputBalance * (inputWeight / outputWeight) * (inputAmount / inputBalance)`. It is not the Soroban transaction fee and is not necessarily the exact fee amount collected by a particular execution; configured swap fees can be higher and integer fee rounding is modeled separately where relevant.

**Adjusted minimum-fee value.** The corresponding minimum-fee comparison scale after including a path-specific source adjustment. In exact-output paths, for example, the contract grosses up the input by dividing through `1 - feeRate`, so the comparison scale includes the same denominator while retaining `MIN_FEE_RATE` as its fee-rate numerator.

**Weighted minimum-fee value.** A minimum-fee comparison scale multiplied by the normalized weight or exponent factors required to express the fee's local effect in the same unit as the entrypoint's adverse error. The exact factor is stated by each theorem rather than assumed to be identical across operations.

**“Less than _p_% of the minimum fee.”** Shorthand for a proved inequality of the form `poolAdverseError < (p / 100) * minimumFeeComparisonValue` on the theorem's stated positive domain. It compares an error with a conservative value derived from the minimum fee; it does not assert that the approximation error is _p_% of the actual fee charged in every execution.

### Arithmetic and proof scope

**`BONE` and one raw unit.** `c_pow` uses `BONE = 10^18` as its fixed-point representation of one. One raw unit therefore represents `10^-18` in the dimensionless `c_pow` value before any entrypoint-specific token scaling.

**Supported operating band.** The proved `c_pow` base interval `[0.5, 1.6]`, within which the baseline series reaches its stopping threshold in at most 46 iterations. Entrypoint-specific low-base cases outside that interval are covered only where the table identifies a separate pool-favoring theorem or bounded execution trace.

**Source-shaped model.** A handwritten Lean function that mirrors the production Rust operation order, checked-arithmetic failures, and branch structure closely enough to compose the arithmetic lemmas at the public-entrypoint boundary. It is not automatically extracted from Rust, so the correspondence assumptions listed in this document remain part of the trusted boundary.

**Machine-checked.** Accepted by the pinned Lean toolchain and declared dependencies without `sorry`, `admit`, or project-defined axioms. This establishes the stated theorem about the Lean model; it does not by itself establish authorization, storage, token-transfer, event, TTL, compiler, runtime, or Rust-to-Lean translation correctness.
