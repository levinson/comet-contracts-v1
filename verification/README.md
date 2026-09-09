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
| The raw recurrence inequality implies the `3k - 2` term budget through iteration 50 | `recurrence_error_budget` |
| The summed scalar budgets equal `(3N² - N) / 2` | `sum_error_budget` |
| `q / (1 - q) <= 1` when `q <= 1/2` | `geometric_tail_le_current` |
| The fractional binomial recurrence implies the exact-term bound `abs(Tₙ) <= S qⁿ` | `fractional_binomial_factor_le_one`, `fractional_binomial_step_contracts`, `fractional_binomial_terms_geometric_bound` |
| Production input/output ratios, fees, and weights retain the `[0.5, 1.6]` operating envelope | Generated `MAX_IN_RATIO`, `MAX_OUT_RATIO`, `MAX_FEE`, and `MAX_WEIGHT`; the `configured_*_margin` and `configured_*_base_*` lemmas in `PoolConfig.lean` |
| Every base in `[0.5, 1.6]` satisfies `abs(x) <= 3/5` | `operating_base_implies_abs_x_le_three_fifths` |
| The computed term reaches production precision by iteration 46 throughout `[0.5, 1.6]`, before the configured cap | `pool_operating_band_numeric_margin`, `pool_operating_band_iteration_within_cap`, `pool_operating_band_converges_by_iteration_46`, `pool_operating_base_converges_by_iteration_46` |
| On the baseline exact-input path, multi-term adverse fractional approximation error is below 10% of the minimum fee's spot-normalized value; the one-term correction has no adverse error | `baseline_exact_input_multiterm_adverse_error_lt_tenth_min_fee`, `baseline_exact_input_first_term_adverse_error_lt_tenth_min_fee` |
| Below-one integer-power composition and a positive output-balance scale preserve the adverse-error fee comparison | `below_one_upper_composition_preserves_adverse_bound`, `positive_output_scale_preserves_fee_comparison` |
| Non-negative directed bounds compose under multiplication | `mul_lower_bound`, `mul_upper_bound` |
| The production Rust precision, exponent, scale, pool-configuration, and iteration constants discharge the proof premises | Generated constants in `GeneratedConstants.lean`; `configured_exponent_limit`, `term_error_at_iteration_cap`, `real_scale_exceeds_term_error_cap`, `sum_error_at_iteration_cap` |
| The final conservative raw product and every recurrence denominator fit signed 256-bit arithmetic | `final_raw_product_fits_i256`, `cpow_raw_magnitude_bound_fits_i256`, `cpow_denominator_bound_fits_i256`, `cpow_denominator_fits_i256` |

## Minimum-fee comparison

For the below-one, round-up fractional path used by an exact-input swap, a one-term result receives the baseline's one-unit upward correction and therefore has no adverse approximation error. If the loop reaches an iteration `N >= 2`, the preceding computed term was greater than `CPOW_PRECISION`. Term contraction by at most `1/2` and the `3k - 2` recurrence-error bound imply

```text
CPOW_PRECISION < abs(T_1) * (1/2)^(N - 2) + (3(N - 1) - 2).
```

For every `2 <= N <= 46`, Lean checks that this threshold forces the complete accumulated rounding budget below `(MIN_FEE / STROOP) * abs(T_1) / 10`. The exact below-one power is no greater than its finite partial sum, so the omitted negative tail cannot increase adverse error. Finally, `abs(T_1) = BONE * fractional_exponent * base_displacement`, while the minimum fee's spot-normalized value is `MIN_FEE_RATE * BONE * full_exponent * nominal_input_ratio`; the fractional exponent does not exceed the full exponent, and the computed base displacement does not exceed the nominal input ratio. This proves the adverse fractional approximation error is below 10% of the minimum fee's continuous spot-normalized output value. The below-one integer factor is at most one and cannot amplify the comparison.

This is a one-sided safety result, not a bound on absolute approximation error. Conservative error may exceed the stated percentage without harming the pool, particularly for very small one-term inputs. Final token-unit quantization is also not part of this theorem.

## Fixed-point implementation refinement

The reusable checked-`I256` model and proofs that the positive-denominator `I256` algorithms refine mathematical floor and ceiling are maintained alongside `src/i256.rs` on the companion `proof/formalize-i256-fixed-point` branch of `soroban-fixed-point-math`. That branch is based on `script3` upstream commit `c85960e`; its source is byte-for-byte identical to the implementation shipped by the exact `soroban-fixed-point-math` 1.5.0 dependency pinned here. This project retains only the `c_pow`-specific magnitude and denominator bounds.

All production fixed-point denominators in `c_pow` are positive. Negative-denominator behavior is therefore outside the proof composition required by this contract.

## Assurance boundary

This project checks supporting mathematical and bounded-integer lemmas, including the adverse-error comparison for the abstract exact-input baseline path, but it does not yet establish a complete error bound for the deployed baseline `c_pow`. The fee comparison is for the approximation itself in continuous spot-normalized output value; it deliberately excludes final token-unit quantization. The remaining work is to formalize the generalized binomial series and its equality to real exponentiation, instantiate the recurrence and final-adjustment lemmas in an executable baseline model, prove the token-scaling and final-integer-rounding layer, mechanically compose this project's operating bounds with the upstream fixed-point refinement theorems, and connect that model to the Rust control flow. The upstream Rust-to-Lean source correspondence is reviewed rather than produced by verified Rust extraction, and primitive Soroban host operations are trusted to satisfy their protocol-specified checked-integer semantics.
