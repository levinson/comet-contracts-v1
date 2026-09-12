import CometCPow.BaselineFeeBound

namespace CometCPow

/-!
Supporting bounds for extending the baseline fee comparison beyond the
exact-input swap path. The theorems in this module remain at the same abstract
continuous-approximation layer as `BaselineFeeBound.lean`.
-/

/-- One percent of the configured minimum swap-fee rate. -/
noncomputable def ONE_PERCENT_MIN_FEE_RATE : ℝ := MIN_FEE_RATE / 100

/-- The generic exact-output second-iteration adverse fee share. -/
noncomputable def EXACT_OUTPUT_SECOND_ITERATION_ADVERSE_FEE_SHARE : ℝ :=
  2 / 125

/-- A practical strict ceiling for ordinary three-fifths-band later error. -/
noncomputable def THREE_FIFTHS_LATER_ADVERSE_FEE_SHARE : ℝ :=
  3961 / 100000

/-- The corresponding finite recurrence rate relative to the first term. -/
noncomputable def THREE_FIFTHS_LATER_FEE_RATE : ℝ :=
  MIN_FEE_RATE * (39601 / 1000000)

/-- A practical strict ceiling for augmented half-band later error. -/
noncomputable def HALF_AUGMENTED_LATER_ADVERSE_FEE_SHARE : ℝ :=
  4751 / 100000

/-- The augmented half-band finite recurrence rate. -/
noncomputable def HALF_AUGMENTED_LATER_FEE_RATE : ℝ :=
  MIN_FEE_RATE * (47501 / 1000000)

theorem one_percent_minimum_fee_rate_value :
    ONE_PERCENT_MIN_FEE_RATE = (1 : ℝ) / 100000000 := by
  norm_num [ONE_PERCENT_MIN_FEE_RATE, MIN_FEE_RATE, MIN_FEE, STROOP]

theorem exact_output_second_iteration_adverse_fee_share_value :
    EXACT_OUTPUT_SECOND_ITERATION_ADVERSE_FEE_SHARE = (2 : ℝ) / 125 := by
  rfl

theorem three_fifths_later_adverse_fee_share_value :
    THREE_FIFTHS_LATER_ADVERSE_FEE_SHARE = (3961 : ℝ) / 100000 := by
  rfl

theorem three_fifths_later_fee_rate_value :
    THREE_FIFTHS_LATER_FEE_RATE = (39601 : ℝ) / 1000000000000 := by
  norm_num [THREE_FIFTHS_LATER_FEE_RATE, MIN_FEE_RATE, MIN_FEE, STROOP]

theorem half_augmented_later_adverse_fee_share_value :
    HALF_AUGMENTED_LATER_ADVERSE_FEE_SHARE = (4751 : ℝ) / 100000 := by
  rfl

theorem half_augmented_later_fee_rate_value :
    HALF_AUGMENTED_LATER_FEE_RATE = (47501 : ℝ) / 1000000000000 := by
  norm_num [HALF_AUGMENTED_LATER_FEE_RATE, MIN_FEE_RATE, MIN_FEE, STROOP]

theorem three_fifths_later_fee_rate_le_selected_share :
    THREE_FIFTHS_LATER_FEE_RATE ≤
      THREE_FIFTHS_LATER_ADVERSE_FEE_SHARE * MIN_FEE_RATE := by
  rw [three_fifths_later_fee_rate_value,
    three_fifths_later_adverse_fee_share_value, minimum_fee_rate_value]
  norm_num

theorem half_augmented_later_fee_rate_le_selected_share :
    HALF_AUGMENTED_LATER_FEE_RATE ≤
      HALF_AUGMENTED_LATER_ADVERSE_FEE_SHARE * MIN_FEE_RATE := by
  rw [half_augmented_later_fee_rate_value,
    half_augmented_later_adverse_fee_share_value, minimum_fee_rate_value]
  norm_num

/-- A dominated first-term scale inherits the selected three-fifths fee share. -/
theorem three_fifths_later_fee_rate_scale_le_selected_share
    {firstTerm feeScale feeValue : ℝ}
    (hfeeScale0 : 0 ≤ feeScale)
    (hfirstScale : firstTerm ≤ feeScale)
    (hfeeValue : feeValue = MIN_FEE_RATE * feeScale) :
    THREE_FIFTHS_LATER_FEE_RATE * firstTerm ≤
      THREE_FIFTHS_LATER_ADVERSE_FEE_SHARE * feeValue := by
  have hrate0 : 0 ≤ THREE_FIFTHS_LATER_FEE_RATE := by
    rw [three_fifths_later_fee_rate_value]
    norm_num
  have hscaled := mul_le_mul_of_nonneg_left hfirstScale hrate0
  have hselected := mul_le_mul_of_nonneg_right
    three_fifths_later_fee_rate_le_selected_share hfeeScale0
  rw [hfeeValue]
  exact le_trans hscaled (by simpa [mul_assoc] using hselected)

/-
The generic geometric estimate discards the division by two in the second
binomial term. Retaining it is what leaves enough margin for above-one paths,
whose configured displacement is close to one half rather than one quarter.
-/

/-- The second fractional-binomial term contracts by at most `q / 2`. -/
theorem fractional_binomial_second_term_contracts
    (T : ℕ → ℝ) {a x q : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hx : |x| ≤ q)
    (hrec : ∀ n,
      T (n + 1) = T n * (a - (n : ℝ)) * x / ((n : ℝ) + 1)) :
    |T 2| ≤ |T 1| * (q / 2) := by
  rw [hrec 1]
  have ha : |a - 1| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  rw [abs_div, abs_mul, abs_mul]
  norm_num
  calc
    |T 1| * |a - 1| * |x| / 2 ≤ |T 1| * 1 * q / 2 := by
      gcongr
    _ = |T 1| * (q / 2) := by ring

/-- Every term after the second inherits the sharper second-term factor. -/
theorem fractional_binomial_terms_from_second_bound
    (T : ℕ → ℝ) {a x q : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hx : |x| ≤ q)
    (hq0 : 0 ≤ q)
    (hrec : ∀ n,
      T (n + 1) = T n * (a - (n : ℝ)) * x / ((n : ℝ) + 1)) :
    ∀ n, |T (n + 2)| ≤ |T 1| * (q / 2) * q ^ n := by
  apply geometric_term_bound
    (M := fun n ↦ |T (n + 2)|)
    (S := |T 1| * (q / 2))
    (fractional_binomial_second_term_contracts T ha0 ha1 hx hrec)
    hq0
  intro n
  rw [show n + 1 + 2 = (n + 2) + 1 by omega, hrec (n + 2)]
  exact fractional_binomial_step_contracts ha0 ha1 hx (n + 2)

/-- The exact second term retains the fee-relevant `(1 - a)` factor. -/
theorem fractional_binomial_second_term_weighted_bound
    (T : ℕ → ℝ) {a x q : ℝ}
    (ha1 : a ≤ 1) (hx : |x| ≤ q)
    (hrec : ∀ n,
      T (n + 1) = T n * (a - (n : ℝ)) * x / ((n : ℝ) + 1)) :
    |T 2| ≤ |T 1| * ((1 - a) * q / 2) := by
  have ht2 : T 2 = T 1 * (a - 1) * x / 2 := by
    have h := hrec 1
    norm_num at h
    exact h
  rw [ht2]
  have hsign : |a - 1| = 1 - a := by
    rw [abs_of_nonpos]
    · ring
    · linarith
  rw [abs_div, abs_mul, abs_mul, hsign, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hfactor0 : 0 ≤ |T 1| * (1 - a) :=
    mul_nonneg (abs_nonneg _) (sub_nonneg.mpr ha1)
  calc
    |T 1| * (1 - a) * |x| / 2 ≤ |T 1| * (1 - a) * q / 2 := by
      gcongr
    _ = |T 1| * ((1 - a) * q / 2) := by ring

/-- Later terms preserve the exact second term's `(1 - a)` factor. -/
theorem fractional_binomial_terms_from_weighted_second_bound
    (T : ℕ → ℝ) {a x q : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hx : |x| ≤ q)
    (hq0 : 0 ≤ q)
    (hrec : ∀ n,
      T (n + 1) = T n * (a - (n : ℝ)) * x / ((n : ℝ) + 1)) :
    ∀ n, |T (n + 2)| ≤ |T 1| * ((1 - a) * q / 2) * q ^ n := by
  apply geometric_term_bound
    (M := fun n ↦ |T (n + 2)|)
    (S := |T 1| * ((1 - a) * q / 2))
    (fractional_binomial_second_term_weighted_bound T ha1 hx hrec)
    hq0
  intro n
  rw [show n + 1 + 2 = (n + 2) + 1 by omega, hrec (n + 2)]
  exact fractional_binomial_step_contracts ha0 ha1 hx (n + 2)

/-- A continued loop exposes the weighted first-term scale paid for by single-sided fees. -/
theorem continued_loop_forces_weighted_first_term_scale
    (T : ℕ → ℝ) {a x previous q : ℝ} {n : ℕ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hx : |x| ≤ q) (hq0 : 0 ≤ q)
    (hrec : ∀ k,
      T (k + 1) = T k * (a - (k : ℝ)) * x / ((k : ℝ) + 1))
    (hn3 : 3 ≤ n)
    (hprevious : (CPOW_PRECISION : ℝ) < |previous|)
    (herror :
      |T (n - 1) - previous| < 3 * ((n - 1 : ℕ) : ℝ) - 2) :
    (CPOW_PRECISION : ℝ) <
      ((1 - a) * |T 1|) * (q / 2) * q ^ (n - 3) +
        (3 * ((n - 1 : ℕ) : ℝ) - 2) := by
  have hterms := fractional_binomial_terms_from_weighted_second_bound
    T ha0 ha1 hx hq0 hrec (n - 3)
  have hindex : n - 3 + 2 = n - 1 := by omega
  rw [hindex] at hterms
  have hcomputed := computed_term_abs_lt herror
  have hrearrange :
      |T 1| * ((1 - a) * q / 2) * q ^ (n - 3) =
        ((1 - a) * |T 1|) * (q / 2) * q ^ (n - 3) := by ring
  rw [hrearrange] at hterms
  linarith

/-- Reaching iteration `n ≥ 3` forces the first term above the sharper scale. -/
theorem continued_loop_forces_sharp_first_term_scale
    (T : ℕ → ℝ) {a x previous q : ℝ} {n : ℕ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hx : |x| ≤ q) (hq0 : 0 ≤ q)
    (hrec : ∀ k,
      T (k + 1) = T k * (a - (k : ℝ)) * x / ((k : ℝ) + 1))
    (hn3 : 3 ≤ n)
    (hprevious : (CPOW_PRECISION : ℝ) < |previous|)
    (herror :
      |T (n - 1) - previous| < 3 * ((n - 1 : ℕ) : ℝ) - 2) :
    (CPOW_PRECISION : ℝ) <
      |T 1| * (q / 2) * q ^ (n - 3) +
        (3 * ((n - 1 : ℕ) : ℝ) - 2) := by
  have hterms := fractional_binomial_terms_from_second_bound
    T ha0 ha1 hx hq0 hrec (n - 3)
  have hindex : n - 3 + 2 = n - 1 := by omega
  rw [hindex] at hterms
  have hcomputed := computed_term_abs_lt herror
  linarith

/-- The three-fifths-band recurrence budget is below `3.9601%` of minimum fee. -/
theorem accumulated_error_lt_three_fifths_later_fee_rate
    {n : ℕ} {firstTerm : ℝ}
    (hn3 : 3 ≤ n) (hn46 : n ≤ 46)
    (hcontinue :
      (CPOW_PRECISION : ℝ) <
        firstTerm * ((3 : ℝ) / 5 / 2) * ((3 : ℝ) / 5) ^ (n - 3) +
          (3 * ((n - 1 : ℕ) : ℝ) - 2)) :
    accumulatedError n < THREE_FIFTHS_LATER_FEE_RATE * firstTerm := by
  interval_cases n <;>
    norm_num [accumulatedError, THREE_FIFTHS_LATER_FEE_RATE, MIN_FEE_RATE,
      MIN_FEE, STROOP, CPOW_PRECISION] at hcontinue ⊢ <;>
    linarith

/-- The same `3.9601%` rate applies to a weighted first-term scale. -/
theorem accumulated_error_lt_three_fifths_weighted_later_fee_rate
    {n : ℕ} {weightedFirstTerm : ℝ}
    (hn3 : 3 ≤ n) (hn46 : n ≤ 46)
    (hcontinue :
      (CPOW_PRECISION : ℝ) <
        weightedFirstTerm * ((3 : ℝ) / 5 / 2) * ((3 : ℝ) / 5) ^ (n - 3) +
          (3 * ((n - 1 : ℕ) : ℝ) - 2)) :
    accumulatedError n < THREE_FIFTHS_LATER_FEE_RATE * weightedFirstTerm := by
  interval_cases n <;>
    norm_num [accumulatedError, THREE_FIFTHS_LATER_FEE_RATE, MIN_FEE_RATE,
      MIN_FEE, STROOP, CPOW_PRECISION] at hcontinue ⊢ <;>
    linarith

/--
At displacement at most one half, the weighted fee also covers the extra
final-term recurrence budget introduced by the below-one round-down path,
which adds its final negative term a second time.
-/
theorem augmented_error_lt_half_later_fee_rate
    {n : ℕ} {weightedFirstTerm : ℝ}
    (hn3 : 3 ≤ n) (hn46 : n ≤ 46)
    (hcontinue :
      (CPOW_PRECISION : ℝ) <
        weightedFirstTerm * ((1 : ℝ) / 2 / 2) * ((1 : ℝ) / 2) ^ (n - 3) +
          (3 * ((n - 1 : ℕ) : ℝ) - 2)) :
    accumulatedError n + (3 * (n : ℝ) - 2) <
      HALF_AUGMENTED_LATER_FEE_RATE * weightedFirstTerm := by
  interval_cases n <;>
    norm_num [accumulatedError, HALF_AUGMENTED_LATER_FEE_RATE, MIN_FEE_RATE,
      MIN_FEE, STROOP, CPOW_PRECISION] at hcontinue ⊢ <;>
    linarith

/-- The exact-output fee covers a one-percent first-term rate at a 1.6% share. -/
theorem exact_output_second_iteration_fee_value_dominates_first_term
    {S a fullExponent q nominalRatio firstTerm feeValue : ℝ}
    (hS0 : 0 ≤ S) (ha0 : 0 ≤ a)
    (haFull : a ≤ fullExponent) (hnominal0 : 0 ≤ nominalRatio)
    (hqNominal : q ≤ (8 / 5 : ℝ) * nominalRatio)
    (hfirst : firstTerm = S * a * q)
    (hfee : feeValue = MIN_FEE_RATE * (S * fullExponent * nominalRatio)) :
    ONE_PERCENT_MIN_FEE_RATE * firstTerm ≤
      EXACT_OUTPUT_SECOND_ITERATION_ADVERSE_FEE_SHARE * feeValue := by
  have hSa0 : 0 ≤ S * a := mul_nonneg hS0 ha0
  have hdisplacement :
      S * a * q ≤ S * a * ((8 / 5 : ℝ) * nominalRatio) :=
    mul_le_mul_of_nonneg_left hqNominal hSa0
  have hscale0 : 0 ≤ S * nominalRatio := mul_nonneg hS0 hnominal0
  have hexponent : S * a * nominalRatio ≤ S * fullExponent * nominalRatio := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left haFull hscale0
  calc
    ONE_PERCENT_MIN_FEE_RATE * firstTerm =
        (1 / 100000000 : ℝ) * (S * a * q) := by
      rw [hfirst, one_percent_minimum_fee_rate_value]
    _ ≤ (1 / 100000000 : ℝ) *
        (S * a * ((8 / 5 : ℝ) * nominalRatio)) :=
      mul_le_mul_of_nonneg_left hdisplacement (by norm_num)
    _ = (2 / 125 : ℝ) *
        ((1 / 1000000 : ℝ) * (S * a * nominalRatio)) := by ring
    _ ≤ (2 / 125 : ℝ) *
        ((1 / 1000000 : ℝ) * (S * fullExponent * nominalRatio)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hexponent (by norm_num)) (by norm_num)
    _ = EXACT_OUTPUT_SECOND_ITERATION_ADVERSE_FEE_SHARE * feeValue := by
      rw [hfee, minimum_fee_rate_value,
        exact_output_second_iteration_adverse_fee_share_value]

/-- A positive exact first term is above every threshold exceeded by its floor. -/
theorem positive_floor_above_threshold
    {rounded : ℤ} {exact threshold : ℝ}
    (hfloor : IsFloor rounded exact)
    (hrounded : threshold < (rounded : ℝ)) :
    threshold < exact :=
  lt_of_lt_of_le hrounded hfloor.le

/--
At iteration two the above-one upper adjustment removes the negative second
term. Only the first term's sub-unit floor error remains, which is below 1.6%
of the corresponding minimum-fee value.
-/
theorem baseline_exact_output_second_iteration_adverse_error_lt_precise_fee_share
    {a fullExponent q nominalRatio firstTerm exactPower exactUpper computedUpper feeValue : ℝ}
    {firstRounded : ℤ}
    (ha0 : 0 ≤ a) (haFull : a ≤ fullExponent)
    (hnominal0 : 0 ≤ nominalRatio)
    (hqNominal : q ≤ (8 / 5 : ℝ) * nominalRatio)
    (hfirst : firstTerm = (BONE : ℝ) * a * q)
    (hfirstFloor : IsFloor firstRounded firstTerm)
    (hcontinued : (CPOW_PRECISION : ℝ) < (firstRounded : ℝ))
    (hexactUpper : exactUpper = (BONE : ℝ) + firstTerm)
    (hcomputedUpper : computedUpper = (BONE : ℝ) + firstRounded)
    (hpower : exactPower ≤ exactUpper)
    (hfeeValue :
      feeValue = MIN_FEE_RATE * ((BONE : ℝ) * fullExponent * nominalRatio)) :
    exactPower - computedUpper <
      EXACT_OUTPUT_SECOND_ITERATION_ADVERSE_FEE_SHARE * feeValue := by
  have hfirstLarge : (CPOW_PRECISION : ℝ) < firstTerm :=
    positive_floor_above_threshold hfirstFloor hcontinued
  have hrounding : exactUpper - computedUpper < 1 := by
    rw [hexactUpper, hcomputedUpper]
    linarith [hfirstFloor.lt_add_one]
  have hadverse : exactPower - computedUpper < 1 := by linarith
  have hfee := exact_output_second_iteration_fee_value_dominates_first_term
    (S := (BONE : ℝ)) (a := a) (fullExponent := fullExponent)
    (q := q) (nominalRatio := nominalRatio)
    (firstTerm := firstTerm) (feeValue := feeValue)
    (by norm_num [BONE]) ha0 haFull hnominal0 hqNominal hfirst hfeeValue
  have hone : 1 < ONE_PERCENT_MIN_FEE_RATE * firstTerm := by
    rw [one_percent_minimum_fee_rate_value]
    norm_num [CPOW_PRECISION] at hfirstLarge ⊢
    linarith
  linarith

/--
Instantiate the configured exact-output base and ratio geometry used by the
second-iteration fractional fee comparison.
-/
theorem baseline_configured_exact_output_second_iteration_adverse_error_lt_precise_fee_share
    {a fullExponent nominalRatio computedBase firstTerm : ℝ}
    {exactPower exactUpper computedUpper feeValue : ℝ}
    {computedBaseRaw firstRounded : ℤ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (haFull : a ≤ fullExponent)
    (hratio0 : 0 ≤ nominalRatio)
    (hratioUpper : nominalRatio ≤ (MAX_OUT_RATIO : ℝ) / STROOP)
    (hbaseLower : 1 ≤ computedBase)
    (hcomputedBase : computedBase = (computedBaseRaw : ℝ) / BONE)
    (hbaseCeil :
      IsCeil computedBaseRaw
        ((BONE : ℝ) * (1 / (1 - nominalRatio))))
    (hfirst : firstTerm = (BONE : ℝ) * a * (computedBase - 1))
    (hfirstFloor : IsFloor firstRounded firstTerm)
    (hcontinued : (CPOW_PRECISION : ℝ) < (firstRounded : ℝ))
    (hexactUpper : exactUpper = (BONE : ℝ) + firstTerm)
    (hcomputedUpper : computedUpper = (BONE : ℝ) + firstRounded)
    (hpower : exactPower ≤ exactUpper)
    (hfeeValue :
      feeValue = MIN_FEE_RATE * ((BONE : ℝ) * fullExponent * nominalRatio)) :
    exactPower - computedUpper <
      EXACT_OUTPUT_SECOND_ITERATION_ADVERSE_FEE_SHARE * feeValue := by
  have hceilScaled := normalized_ceil_lt_exact_add_inv_scale
    (exact := 1 / (1 - nominalRatio)) (by norm_num [BONE]) hbaseCeil
  have hceil :
      computedBase < 1 / (1 - nominalRatio) + 1 / (BONE : ℝ) := by
    rw [hcomputedBase]
    exact hceilScaled
  have hfirstLarge : (CPOW_PRECISION : ℝ) < firstTerm :=
    positive_floor_above_threshold hfirstFloor hcontinued
  have hratioLower := continued_exact_output_forces_nominal_ratio_lower
    hratio0 hratioUpper hbaseLower hceil ha1 hfirst hfirstLarge
  have hbounds := configured_exact_output_computed_bounds
    hratioLower hratioUpper hbaseLower hceil
  exact baseline_exact_output_second_iteration_adverse_error_lt_precise_fee_share
    ha0 haFull hratio0 hbounds.2 hfirst hfirstFloor hcontinued
      hexactUpper hcomputedUpper hpower hfeeValue

/-- The one-term upward correction is conservative for an above-one fractional power. -/
theorem baseline_exact_output_first_iteration_has_no_adverse_error
    {firstTerm exactPower exactUpper computedUpper : ℝ} {firstRounded : ℤ}
    (hfirstFloor : IsFloor firstRounded firstTerm)
    (hexactUpper : exactUpper = (BONE : ℝ) + firstTerm)
    (hcomputedUpper : computedUpper = (BONE : ℝ) + firstRounded + 1)
    (hpower : exactPower ≤ exactUpper) :
    exactPower ≤ computedUpper := by
  rw [hexactUpper] at hpower
  rw [hcomputedUpper]
  linarith [hfirstFloor.lt_add_one]

/--
Generic later-iteration comparison for any operation in the full operating
band whose fee scale directly dominates the first fractional term.
-/
theorem baseline_operating_band_later_adverse_error_lt_precise_fee_share
    (T : ℕ → ℝ)
    {n : ℕ} {a x previous firstTerm : ℝ}
    {exactPower exactUpper computedUpper feeValue : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hx : |x| ≤ (3 : ℝ) / 5)
    (hrec : ∀ k,
      T (k + 1) = T k * (a - (k : ℝ)) * x / ((k : ℝ) + 1))
    (hn3 : 3 ≤ n) (hn46 : n ≤ 46)
    (hprevious : (CPOW_PRECISION : ℝ) < |previous|)
    (htermError :
      |T (n - 1) - previous| < 3 * ((n - 1 : ℕ) : ℝ) - 2)
    (hfirst : firstTerm = |T 1|)
    (hpower : exactPower ≤ exactUpper)
    (hsum : |exactUpper - computedUpper| < accumulatedError n)
    (hfee : THREE_FIFTHS_LATER_FEE_RATE * firstTerm ≤
      THREE_FIFTHS_LATER_ADVERSE_FEE_SHARE * feeValue) :
    exactPower - computedUpper <
      THREE_FIFTHS_LATER_ADVERSE_FEE_SHARE * feeValue := by
  have hcontinue := continued_loop_forces_sharp_first_term_scale
    T ha0 ha1 hx (by norm_num) hrec hn3 hprevious htermError
  rw [← hfirst] at hcontinue
  have hbudget := accumulated_error_lt_three_fifths_later_fee_rate
    hn3 hn46 (by simpa using hcontinue)
  have hadverse : exactPower - computedUpper < accumulatedError n := by
    have hupper : exactUpper - computedUpper < accumulatedError n :=
      lt_of_le_of_lt (le_abs_self (exactUpper - computedUpper)) hsum
    linarith
  linarith

/-- The single-sided weighted fee scale dominates the reciprocal exponent's fractional term. -/
theorem single_sided_fee_value_dominates_reciprocal_fractional_term_precise
    {S fractional weight q nominalRatio firstTerm feeValue : ℝ}
    (hS0 : 0 ≤ S) (hfractional0 : 0 ≤ fractional)
    (hfractionalFee : fractional ≤ (1 - weight) / weight)
    (hnominal0 : 0 ≤ nominalRatio) (hqNominal : q ≤ nominalRatio)
    (hfirst : firstTerm = S * fractional * q)
    (hfee :
      feeValue = MIN_FEE_RATE * (S * ((1 - weight) / weight) * nominalRatio)) :
    THREE_FIFTHS_LATER_FEE_RATE * firstTerm ≤
      THREE_FIFTHS_LATER_ADVERSE_FEE_SHARE * feeValue := by
  have hSf0 : 0 ≤ S * fractional := mul_nonneg hS0 hfractional0
  have hdisplacement : S * fractional * q ≤ S * fractional * nominalRatio :=
    mul_le_mul_of_nonneg_left hqNominal hSf0
  have hscale0 : 0 ≤ S * nominalRatio := mul_nonneg hS0 hnominal0
  have hexponent :
      S * fractional * nominalRatio ≤
        S * ((1 - weight) / weight) * nominalRatio := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left hfractionalFee hscale0
  have hfirstScale :
      firstTerm ≤ S * ((1 - weight) / weight) * nominalRatio := by
    rw [hfirst]
    exact le_trans hdisplacement hexponent
  have hfeeScale0 :
      0 ≤ S * ((1 - weight) / weight) * nominalRatio :=
    mul_nonneg (mul_nonneg hS0 (le_trans hfractional0 hfractionalFee))
      hnominal0
  exact three_fifths_later_fee_rate_scale_le_selected_share
    hfeeScale0 hfirstScale hfee

/-- A direct single-sided fee dominates the `(1 - weight)`-weighted first term. -/
theorem single_sided_fee_value_dominates_weighted_first_term_precise
    {S weight q nominalRatio firstTerm feeValue : ℝ}
    (hS0 : 0 ≤ S) (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1)
    (hnominal0 : 0 ≤ nominalRatio) (hqNominal : q ≤ nominalRatio)
    (hfirst : firstTerm = S * weight * q)
    (hfee :
      feeValue = MIN_FEE_RATE * (S * weight * (1 - weight) * nominalRatio)) :
    THREE_FIFTHS_LATER_FEE_RATE * ((1 - weight) * firstTerm) ≤
      THREE_FIFTHS_LATER_ADVERSE_FEE_SHARE * feeValue := by
  have hSw0 : 0 ≤ S * weight := mul_nonneg hS0 hweight0
  have hfactor0 : 0 ≤ S * weight * (1 - weight) :=
    mul_nonneg hSw0 (sub_nonneg.mpr hweight1)
  have hratio :
      S * weight * (1 - weight) * q ≤
        S * weight * (1 - weight) * nominalRatio :=
    mul_le_mul_of_nonneg_left hqNominal hfactor0
  have hfirstScale :
      (1 - weight) * firstTerm ≤
        S * weight * (1 - weight) * nominalRatio := by
    rw [hfirst]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hratio
  have hfeeScale0 :
      0 ≤ S * weight * (1 - weight) * nominalRatio :=
    mul_nonneg hfactor0 hnominal0
  exact three_fifths_later_fee_rate_scale_le_selected_share
    hfeeScale0 hfirstScale hfee

/--
Later direct single-sided paths have less than 3.961% adverse continuous
approximation error, even without assuming that the selected directional
result stayed on the conservative side.
-/
theorem baseline_direct_single_sided_later_adverse_error_lt_precise_fee_share
    (T : ℕ → ℝ)
    {n : ℕ} {weight x previous q nominalRatio : ℝ}
    {exactPower exactDirectional computedDirectional feeValue : ℝ}
    (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1)
    (hx : |x| ≤ (3 : ℝ) / 5)
    (hrec : ∀ k,
      T (k + 1) = T k * (weight - (k : ℝ)) * x / ((k : ℝ) + 1))
    (hn3 : 3 ≤ n) (hn46 : n ≤ 46)
    (hprevious : (CPOW_PRECISION : ℝ) < |previous|)
    (htermError :
      |T (n - 1) - previous| < 3 * ((n - 1 : ℕ) : ℝ) - 2)
    (hfirst : |T 1| = (BONE : ℝ) * weight * q)
    (hnominal0 : 0 ≤ nominalRatio) (hqNominal : q ≤ nominalRatio)
    (hfeeValue :
      feeValue =
        MIN_FEE_RATE * ((BONE : ℝ) * weight * (1 - weight) * nominalRatio))
    (hdirectional : exactDirectional ≤ exactPower)
    (hsum : |computedDirectional - exactDirectional| < accumulatedError n) :
    computedDirectional - exactPower <
      THREE_FIFTHS_LATER_ADVERSE_FEE_SHARE * feeValue := by
  have hcontinue := continued_loop_forces_weighted_first_term_scale
    T hweight0 hweight1 hx (by norm_num) hrec hn3 hprevious htermError
  have hbudget :=
    accumulated_error_lt_three_fifths_weighted_later_fee_rate
      hn3 hn46 (by simpa using hcontinue)
  have hadverse : computedDirectional - exactPower < accumulatedError n := by
    have hrounded : computedDirectional - exactDirectional < accumulatedError n :=
      lt_of_le_of_lt (le_abs_self (computedDirectional - exactDirectional)) hsum
    linarith
  have hfee := single_sided_fee_value_dominates_weighted_first_term_precise
    (S := (BONE : ℝ)) (weight := weight) (q := q)
    (nominalRatio := nominalRatio) (firstTerm := |T 1|) (feeValue := feeValue)
    (by norm_num [BONE]) hweight0 hweight1 hnominal0 hqNominal hfirst hfeeValue
  linarith

/-- The reciprocal exponent's fractional part is paid for by the single-sided fee factor. -/
theorem reciprocal_fractional_part_le_fee_exponent
    {weight fractional integerPart : ℝ}
    (hweight0 : 0 < weight)
    (hinteger : 1 ≤ integerPart)
    (hsplit : 1 / weight = integerPart + fractional) :
    fractional ≤ (1 - weight) / weight := by
  have hreciprocal : fractional ≤ 1 / weight - 1 := by linarith
  have hid : 1 / weight - 1 = (1 - weight) / weight := by
    field_simp
  rw [hid] at hreciprocal
  exact hreciprocal

/--
Composition of the reciprocal-exponent identity, weighted fee scale, sharp
operating-band estimate, and later-iteration adverse-error bound.
-/
theorem baseline_reciprocal_single_sided_later_adverse_error_lt_precise_fee_share
    (T : ℕ → ℝ)
    {n : ℕ} {weight fractional integerPart x previous q nominalRatio : ℝ}
    {exactPower exactUpper computedUpper feeValue : ℝ}
    (hweight0 : 0 < weight)
    (hfractional0 : 0 ≤ fractional) (hfractional1 : fractional ≤ 1)
    (hinteger : 1 ≤ integerPart)
    (hsplit : 1 / weight = integerPart + fractional)
    (hx : |x| ≤ (3 : ℝ) / 5)
    (hrec : ∀ k,
      T (k + 1) = T k * (fractional - (k : ℝ)) * x / ((k : ℝ) + 1))
    (hn3 : 3 ≤ n) (hn46 : n ≤ 46)
    (hprevious : (CPOW_PRECISION : ℝ) < |previous|)
    (htermError :
      |T (n - 1) - previous| < 3 * ((n - 1 : ℕ) : ℝ) - 2)
    (hfirst : |T 1| = (BONE : ℝ) * fractional * q)
    (hnominal0 : 0 ≤ nominalRatio) (hqNominal : q ≤ nominalRatio)
    (hfeeValue :
      feeValue = MIN_FEE_RATE *
        ((BONE : ℝ) * ((1 - weight) / weight) * nominalRatio))
    (hpower : exactPower ≤ exactUpper)
    (hsum : |exactUpper - computedUpper| < accumulatedError n) :
    exactPower - computedUpper <
      THREE_FIFTHS_LATER_ADVERSE_FEE_SHARE * feeValue := by
  have hfractionalFee := reciprocal_fractional_part_le_fee_exponent
    hweight0 hinteger hsplit
  have hfee := single_sided_fee_value_dominates_reciprocal_fractional_term_precise
    (S := (BONE : ℝ)) (fractional := fractional) (weight := weight)
    (q := q) (nominalRatio := nominalRatio) (firstTerm := |T 1|)
    (feeValue := feeValue) (by norm_num [BONE]) hfractional0
    hfractionalFee hnominal0 hqNominal hfirst hfeeValue
  exact baseline_operating_band_later_adverse_error_lt_precise_fee_share
    T hfractional0 hfractional1 hx hrec hn3 hn46 hprevious htermError
      rfl hpower hsum hfee

/-- Directed rounding in a proportional join cannot require less than the exact deposit. -/
theorem proportional_join_rounding_is_pool_favoring
    {balance exactRatio roundedRatio roundedDeposit : ℝ}
    (hbalance0 : 0 ≤ balance)
    (hratioUpper : exactRatio ≤ roundedRatio)
    (hdepositUpper : balance * roundedRatio ≤ roundedDeposit) :
    balance * exactRatio ≤ roundedDeposit := by
  calc
    balance * exactRatio ≤ balance * roundedRatio :=
      mul_le_mul_of_nonneg_left hratioUpper hbalance0
    _ ≤ roundedDeposit := hdepositUpper

/-- Directed rounding in a proportional exit cannot return more than the exact withdrawal. -/
theorem proportional_exit_rounding_is_pool_favoring
    {balance exactRatio roundedRatio roundedWithdrawal : ℝ}
    (hbalance0 : 0 ≤ balance)
    (hratioLower : roundedRatio ≤ exactRatio)
    (hwithdrawalLower : roundedWithdrawal ≤ balance * roundedRatio) :
    roundedWithdrawal ≤ balance * exactRatio := by
  calc
    roundedWithdrawal ≤ balance * roundedRatio := hwithdrawalLower
    _ ≤ balance * exactRatio := mul_le_mul_of_nonneg_left hratioLower hbalance0

/-- Exact ceiling refinements compose into the pool-favoring proportional-join bound. -/
theorem proportional_join_ceil_chain_is_pool_favoring
    {balance exactRatio : ℝ} {roundedRatio roundedDeposit : ℤ}
    (hbalance0 : 0 ≤ balance)
    (hratioCeil : IsCeil roundedRatio exactRatio)
    (hdepositCeil : IsCeil roundedDeposit (balance * roundedRatio)) :
    balance * exactRatio ≤ (roundedDeposit : ℝ) :=
  proportional_join_rounding_is_pool_favoring
    hbalance0 hratioCeil.le hdepositCeil.le

/-- Exact floor refinements compose into the pool-favoring proportional-exit bound. -/
theorem proportional_exit_floor_chain_is_pool_favoring
    {balance exactRatio : ℝ} {roundedRatio roundedWithdrawal : ℤ}
    (hbalance0 : 0 ≤ balance)
    (hratioFloor : IsFloor roundedRatio exactRatio)
    (hwithdrawalFloor : IsFloor roundedWithdrawal (balance * roundedRatio)) :
    (roundedWithdrawal : ℝ) ≤ balance * exactRatio :=
  proportional_exit_rounding_is_pool_favoring
    hbalance0 hratioFloor.le hwithdrawalFloor.le

end CometCPow
