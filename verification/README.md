# Machine-checked c_pow lemmas

This Lean project machine-checks the baseline `c_pow` recurrence-error budget, geometric-tail simplification, operating-band convergence, composition, configured limits, and application-specific signed-`I256` magnitude and denominator bounds.

The checked-in Lean constants are generated from the production Rust constants,
so the proof cannot silently keep using old pool ratios, fees, weights,
precision, exponent, or iteration limits. From the repository root, check that
the generated module is current with:

```sh
rustc --edition=2021 verification/generate_constants.rs -o /tmp/generate-cpow-constants
/tmp/generate-cpow-constants --check verification/CometCPow/GeneratedConstants.lean
```

To regenerate it after changing a source constant, replace the `--check` line
with:

```sh
/tmp/generate-cpow-constants > verification/CometCPow/GeneratedConstants.lean
```

Then run the proofs with:

```sh
cd verification
lake update
lake build
```

The project pins Lean and mathlib to version 4.19.0. The
`c_pow formal verification` workflow first rejects a stale generated constants
module, then runs the build for every relevant pull-request change and rejects
proof sources containing `sorry`, `admit`, or custom `axiom` declarations. It
also audits the compiled `CometCPow` namespace transitively, allowing only
Lean's standard `propext`, `Classical.choice`, and `Quot.sound` foundations.

The verification project is development-only. It is not a dependency of any
Rust crate and does not alter the contract's instructions, memory use, or WASM
size.

## Checked claims

| Proof obligation | Lean theorem |
| --- | --- |
| Mathematical floor/ceiling errors are below one raw unit | `floor_isFloor`, `ceil_isCeil`, `IsFloor.abs_error_lt_one`, `IsCeil.abs_error_lt_one` |
| One recurrence step adds less than three raw units | `recurrence_increment_lt_three` |
| The three exact floors in a concrete baseline recurrence update imply the raw one-step error inequality | `three_floor_recurrence_step_error` |
| The raw recurrence inequality implies the `3k - 2` term budget through iteration 50 | `recurrence_error_budget` |
| The summed scalar budgets equal `(3N² - N) / 2` | `sum_error_budget` |
| The per-step recurrence inequality and first floor refinement imply the complete finite-partial-sum error budget | `partial_sum_error_lt_sum_error_budget`, `recurrence_implies_partial_sum_error_budget` |
| `q / (1 - q) <= 1` when `q <= 1/2` | `geometric_tail_le_current` |
| The fractional binomial recurrence implies the exact-term bound `abs(Tₙ) <= S qⁿ` | `fractional_binomial_factor_le_one`, `fractional_binomial_step_contracts`, `fractional_binomial_terms_geometric_bound` |
| Taylor's theorem identifies the exact generalized-binomial terms and proves every finite below-one partial sum upper-bounds real exponentiation for fractional exponents in `[0,1]` | `iteratedDerivWithin_one_sub_rpow`, `bone_mul_taylorWithinEval_eq_exactInputBinomialSum`, `exact_input_binomial_partial_upper` |
| Production input/output ratios, fees, and weights retain the `[0.5, 1.6]` operating envelope | Generated `MAX_IN_RATIO`, `MAX_OUT_RATIO`, `MAX_FEE`, and `MAX_WEIGHT`; the `configured_*_margin` and `configured_*_base_*` lemmas in `PoolConfig.lean` |
| Every base in `[0.5, 1.6]` satisfies `abs(x) <= 3/5` | `operating_base_implies_abs_x_le_three_fifths` |
| The computed term reaches production precision by iteration 46 throughout `[0.5, 1.6]`, before the configured cap | `pool_operating_band_numeric_margin`, `pool_operating_band_iteration_within_cap`, `pool_operating_band_converges_by_iteration_46`, `pool_operating_base_converges_by_iteration_46` |
| On the baseline exact-input path, multi-term adverse fractional approximation error is below 5% of the minimum fee's spot-normalized value; the one-term correction has no adverse error | `baseline_exact_input_multiterm_adverse_error_lt_five_percent_min_fee`, `first_term_upper_has_no_adverse_error` |
| The exact-input caller's input floor, base ceiling, exponent floor, integer/fractional `c_pow` composition, output multiplication floor, and token downscale compose into the same 5% bound for integer-only, unit-base, corrected first-term, and multi-term control-flow cases | `baseline_swap_exact_amount_in_integer_adverse_error_lt_five_percent_min_fee`, `baseline_swap_exact_amount_in_unit_base_adverse_error_lt_five_percent_min_fee`, `baseline_swap_exact_amount_in_first_term_adverse_error_lt_five_percent_min_fee`, `baseline_swap_exact_amount_in_multiterm_adverse_error_lt_five_percent_min_fee` |
| Below-one integer-power composition and a positive output-balance scale preserve the adverse-error fee comparison | `below_one_upper_composition_preserves_adverse_bound`, `positive_output_scale_preserves_fee_comparison` |
| An exponentiation-by-squaring trace whose multiplications use exact ceiling refinements upper-bounds the natural power computed by `c_powi` | `UpperCPowiLoop.upper_bound`, `UpperCPowiTrace.upper_bound`, `normalized_mul_ceil_upper` |
| Retaining the exact `1/2` contraction in the second binomial term gives a 5% first-term fee margin throughout the full operating band | `fractional_binomial_second_term_contracts`, `fractional_binomial_terms_from_second_bound`, `accumulated_error_lt_five_percent_min_fee_of_later_terms` |
| At the abstract recurrence/fixed-point premise layer, the fractional exact-output first-iteration correction has no adverse error, the configured second-iteration case leaves less than 5% fee-relative adverse error, and configured later iterations remain below 5%; the configuration bridge derives the required displacement-to-ratio bound from the generated ratio limit, an exact ceiling refinement, and continuation | `baseline_exact_output_first_iteration_has_no_adverse_error`, `baseline_configured_exact_output_second_iteration_adverse_error_lt_five_percent_min_fee`, `baseline_configured_exact_output_later_adverse_error_lt_five_percent_min_fee`, `configured_exact_output_computed_bounds`, `continued_exact_output_forces_nominal_ratio_lower` |
| At the abstract recurrence layer, the reciprocal exponent's fractional part is bounded by the single-sided weighted-fee exponent, and the conditional later reciprocal single-sided fractional result remains below 5% | `reciprocal_fractional_part_le_fee_exponent`, `single_sided_fee_value_dominates_reciprocal_fractional_term`, `baseline_reciprocal_single_sided_later_adverse_error_lt_five_percent_min_fee` |
| At the abstract recurrence layer, the exact `(1 - weight)` second-term factor makes the conditional later direct single-sided adverse error smaller than 5% of the weighted minimum fee | `fractional_binomial_second_term_weighted_bound`, `accumulated_error_lt_five_percent_min_fee_of_weighted_later_terms`, `baseline_direct_single_sided_later_adverse_error_lt_five_percent_min_fee` |
| Exact ceiling/floor refinements compose algebraically into pool-favoring proportional join/exit bounds | `proportional_join_ceil_chain_is_pool_favoring`, `proportional_exit_floor_chain_is_pool_favoring` |
| Non-negative directed bounds compose under multiplication | `mul_lower_bound`, `mul_upper_bound` |
| The production Rust precision, exponent, scale, pool-configuration, and iteration constants discharge the proof premises | Generated constants in `GeneratedConstants.lean`; `configured_exponent_limit`, `term_error_at_iteration_cap`, `real_scale_exceeds_term_error_cap`, `sum_error_at_iteration_cap` |
| The final conservative raw product and every recurrence denominator fit signed 256-bit arithmetic | `final_raw_product_fits_i256`, `cpow_raw_magnitude_bound_fits_i256`, `cpow_denominator_bound_fits_i256`, `cpow_denominator_fits_i256` |

## Minimum-fee comparison

For the below-one, round-up fractional path used by an exact-input swap, a one-term result receives the baseline's one-unit upward correction and therefore has no adverse approximation error. If the loop reaches an iteration `N >= 2`, the preceding computed term was greater than `CPOW_PRECISION`. The configured maximum input ratio and minimum fee sharpen the exact-input contraction factor to strictly less than `1/4`, so the `3k - 2` recurrence-error bound implies

```text
CPOW_PRECISION < abs(T_1) * (1/4)^(N - 2) + (3(N - 1) - 2).
```

For every `2 <= N <= 46`, Lean checks that this continuation threshold forces the complete accumulated rounding budget below `(MIN_FEE / STROOP) * abs(T_1) / 20`. At `N = 2`, where the finite table reaches its maximum fee share, the sign-specific first-term floor property proves `CPOW_PRECISION < abs(T_1)` without the generic one-unit error slack. A Taylor-remainder proof derives the generalized-binomial recurrence from the derivatives of `(1 - q)^a` and proves every finite partial sum is an upper bound on the exact below-one power, so the omitted negative tail cannot increase adverse error. Finally, `abs(T_1) = BONE * fractional_exponent * base_displacement`, while the minimum fee's spot-normalized value is `MIN_FEE_RATE * BONE * full_exponent * nominal_input_ratio`; the fractional exponent does not exceed the full exponent, and the computed base displacement does not exceed the nominal input ratio. This proves the adverse fractional approximation error is strictly below 5% of the minimum fee's continuous spot-normalized output value. The below-one integer factor is at most one and cannot amplify the comparison.

The operation-level theorems instantiate the exact-input caller's fee-adjusted input floor, normalized base ceiling, weight-ratio exponent floor, below-one integer/fractional composition, final output multiplication floor, and token downscale floor. They cover an integer exponent, the degenerate unit-base fractional result for which the implementation intentionally skips its one-unit correction, a non-unit fractional path that stops after its first term, and a fractional path that reaches a later term. In the multi-term case, the three floor refinements derive the per-step recurrence inequality, which derives the aggregate partial-sum and previous-term bounds. The iteration-46 convergence theorem is then applied to the same computed-term trace, so `N <= 46` follows from the loop continuation condition instead of appearing as an independent premise.

This is a one-sided safety result, not a bound on absolute approximation error. Conservative error may exceed the stated percentage without harming the pool, particularly for very small one-term inputs. The final token-unit floors are included directionally because they can only decrease the user-visible exact-input output; the fee denominator remains the minimum fee's continuous spot-normalized value.

## Additional operation paths

The exact-output fractional path has a larger base displacement than exact input. Lean composes the generated maximum-output ratio, a mathematical `IsCeil` refinement of the normalized base, and the continued-loop threshold: after including a complete raw ceiling unit, the computed base is below `1.51`, so `abs(base - 1) < 0.51`; if the loop reaches a fee-relevant second or later iteration, continuation forces the nominal ratio above the tiny value needed to absorb that ceiling unit and proves `base - 1 <= (8/5) * nominal_ratio`. The generic geometric proof was too coarse to establish a 5% ceiling there because it discarded the division by two in the second binomial term. `OperationFeeBound.lean` retains that factor. It proves the one-term upward correction conservative, bounds the iteration-two adjusted result by the first term's sub-unit floor error, and proves the later-iteration accumulated budget is below one thirty-second of the first-term minimum-fee scale. The configured displacement-to-ratio bridge then yields the 5% fractional-result comparison.

Single-sided operations charge the weighted fee `(1 - weight) * swap_fee`. For reciprocal exponents, Lean proves that the fractional part of `1 / weight` is at most `(1 - weight) / weight`, so the smaller fee and reciprocal exponent compensate algebraically. For direct weight exponents, the exact second term contains the same `(1 - weight)` factor as the fee; retaining that factor proves the later-iteration adverse error is below 5% across the full operating band. These results cover the continuous fractional comparison under explicit recurrence, stopping, tail-direction, and fixed-point error premises. Early direct round-down cases and the final operation-level composition for above-one whole powers still require executable-model instantiation before the complete join and withdrawal entry points can carry an unconditional 5% theorem.

Ordinary proportional `join_pool` and `exit_pool` do not call `c_pow` and do not charge a swap fee. Their relevant property is instead zero adverse rounding direction: Lean proves that exact `IsCeil` refinements for the join ratio and deposit compose so the join cannot undercharge, and exact `IsFloor` refinements for the exit ratio and withdrawal compose so the exit cannot overpay. Instantiating those refinements from the Rust fixed-point calls remains part of the source-correspondence boundary below.

## Fixed-point implementation refinement

The reusable checked-`I256` model and proofs that the positive-denominator `I256` algorithms refine mathematical floor and ceiling are maintained alongside `src/i256.rs` on the companion `proof/formalize-i256-fixed-point` branch of `soroban-fixed-point-math`, pinned here to proof commit [`649f02a`](https://github.com/blnt-protocol/soroban-fixed-point-math/commit/649f02aab503e0502f495b64de5575da2c28434b). That proof commit is based on `script3` upstream commit `c85960e`; its source is byte-for-byte identical to the implementation shipped by the exact `soroban-fixed-point-math` 1.5.0 dependency pinned here. This project retains only the `c_pow`-specific magnitude and denominator bounds.

All production fixed-point denominators in `c_pow` are positive. Negative-denominator behavior is therefore outside the proof composition required by this contract.

## Assurance boundary

For `swap_exact_amount_in`, this project now completes the operation-level mathematical composition for the integer-only, unit-base, corrected first-term, and multi-term paths. It includes the generalized-binomial tail direction, the three mathematical floors in every fractional recurrence update, an exponentiation-by-squaring trace for upper-rounded `c_powi`, the final upper-rounded `c_pow` multiplication, directional token scaling, and final integer floors. The exact-input entry theorems consume explicit loop traces and mathematical `IsFloor`/`IsCeil` refinements rather than assuming the resulting high-level error or direction bounds.

The project does not yet establish a complete error bound for every other deployed baseline `c_pow` caller. For exact input, the remaining assurance boundary is source correspondence: constructing the checked loop traces from the deployed Rust control flow and mechanically composing each mathematical floor/ceiling premise with the companion fixed-point implementation-refinement theorem. Other operations still need their early direct round-down and above-one whole-power compositions. Rust-to-Lean correspondence is reviewed rather than produced by verified Rust extraction, and primitive Soroban host operations are trusted to satisfy their protocol-specified checked-integer semantics.
