# Machine-check baseline `c_pow` convergence and fee-relative adverse error

## Summary

This PR adds a development-only Lean 4 verification project for the unchanged baseline `c_pow` design on `update-and-review`. It machine-checks the supporting recurrence, operating-band, configured-limit, fixed-point composition, and bounded-I256 results; proves that the computed term reaches `CPOW_PRECISION` by iteration 46 throughout the supported `[0.5, 1.6]` base band; proves that adverse continuous approximation error on the abstract exact-input path is strictly below 5% of the minimum fee's spot-normalized value; and adds supporting 5% bounds for the fractional exact-output and single-sided paths while proving proportional join/exit rounding is pool-favoring.

## Changes

- Add a pinned Lean 4.19/mathlib verification project under `verification/`.
- Generate Lean configuration constants from the production Rust constants and reject stale generated values in CI.
- Add compile-time guards that keep the exponent, iteration, precision, ratio, weight, and fee assumptions synchronized with the proof.
- Pin `soroban-fixed-point-math` to the exact currently resolved version and prove the application-specific I256 magnitude and denominator bounds needed at the `c_pow` boundary.
- Add CI checks that build the proof, reject `sorry`, `admit`, and custom axioms, and audit the resulting declarations' axioms.

## Machine-checked results

- Mathematical floor and ceiling operations introduce less than one raw unit of error.
- The recurrence error budget is `3k - 2`, and its accumulated sum through `N` terms is `(3N² - N) / 2`.
- Pool configuration constrains successful-operation bases to `[0.5, 1.6]`.
- The recurrence term reaches `CPOW_PRECISION` by iteration 46 across that band, before the implementation's 50-iteration cap.
- On the exact-input path, the one-term directional correction has zero adverse approximation error, while every applicable multi-term case has adverse continuous approximation error strictly below 5% of the minimum fee's spot-normalized value.
- Integer below-one power composition and positive output-balance scaling do not amplify the adverse fee comparison.
- Retaining the exact second-term contraction establishes the 5% numerical margin needed by above-one and weighted-fee paths.
- At the abstract recurrence/fixed-point premise layer, the fractional exact-output path has zero first-iteration adverse error and less than 5% fee-relative adverse error at iteration two and later; the configured cases derive their base displacement and fee geometry from the generated output-ratio limit, an exact ceiling refinement, and continuation.
- At the abstract recurrence layer, conditional later reciprocal and direct single-sided fractional results remain below 5% of their weighted minimum-fee scales.
- Proportional joins and exits do not invoke `c_pow`; exact ceiling/floor refinements compose algebraically into pool-favoring rounding bounds.

## Runtime impact

The PR does not change the runtime `c_pow` arithmetic or add runtime operations. Lean is a development-only dependency, the synchronization guards are compile-time checks, and the fixed-point dependency pin selects the version already used by the project.

## Assurance boundary

The fee theorems are one-sided: they bound error adverse to the pool, not absolute approximation error. Exact input has the most complete abstract composition; the additional exact-output and single-sided results currently establish supporting fractional-path obligations rather than unconditional end-to-end guarantees for every entry point. The configured exact-output theorems discharge the production constant, base-ceiling, and nominal-ratio geometry, but still assume the documented abstract recurrence, stopping, tail-direction, and accumulated-error premises. The proportional results compose exact mathematical ceiling/floor refinements but do not independently verify that the Rust calls implement those refinements. Early direct round-down cases, above-one whole-power operation composition, and final token-unit quantization remain outside the completed 5% result. This is not yet an end-to-end proof of the deployed Rust implementation: completing that proof would require connecting the generalized binomial series to real exponentiation, instantiating an executable model of the baseline control flow, composing the upstream fixed-point refinement, and proving the remaining token-scaling and source-correspondence steps. Rust control-flow correspondence remains review-based, and the underlying host integer operations remain trusted.

## Validation

- `lake build`
- Generated-constant freshness check
- Proof escape-hatch and axiom audit
- `cargo check -p contracts`
