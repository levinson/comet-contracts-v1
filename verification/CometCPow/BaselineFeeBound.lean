import CometCPow.OperatingBand
import CometCPow.FixedPoint

namespace CometCPow

/-!
Supporting theorems for comparing the baseline exact-input `c_pow`
approximation error with the minimum swap fee in a common, dimensionless
output-value normalization.

These theorems cover the `base < 1`, `round_up = true` fractional path used by
`calc_token_out_given_token_in`. They deliberately distinguish the
approximation error from final token-unit rounding.
-/

/-- The configured minimum swap-fee rate. -/
noncomputable def MIN_FEE_RATE : ℝ := (MIN_FEE : ℝ) / STROOP

/-- Ten percent of the configured minimum swap-fee rate. -/
noncomputable def TENTH_MIN_FEE_RATE : ℝ := MIN_FEE_RATE / 10

/-- Five percent of the configured minimum swap-fee rate. -/
noncomputable def FIVE_PERCENT_MIN_FEE_RATE : ℝ := MIN_FEE_RATE / 20

/-- The closed-form accumulated recurrence-rounding budget through term `n`. -/
noncomputable def accumulatedError (n : ℕ) : ℝ := (3 * (n : ℝ) ^ 2 - n) / 2

theorem minimum_fee_rate_value : MIN_FEE_RATE = (1 : ℝ) / 1000000 := by
  norm_num [MIN_FEE_RATE, MIN_FEE, STROOP]

theorem tenth_minimum_fee_rate_value : TENTH_MIN_FEE_RATE = (1 : ℝ) / 10000000 := by
  norm_num [TENTH_MIN_FEE_RATE, MIN_FEE_RATE, MIN_FEE, STROOP]

theorem five_percent_minimum_fee_rate_value :
    FIVE_PERCENT_MIN_FEE_RATE = (1 : ℝ) / 20000000 := by
  norm_num [FIVE_PERCENT_MIN_FEE_RATE, MIN_FEE_RATE, MIN_FEE, STROOP]

/--
If iteration `n` is reached, term `n - 1` was still above the stopping
precision. Geometric contraction then forces the first exact term to be large
enough that ten percent of the minimum fee scale exceeds the entire
accumulated recurrence-rounding budget.
-/
theorem accumulated_error_lt_tenth_min_fee_of_multiterm
    {n : ℕ} {firstTerm : ℝ}
    (hn2 : 2 ≤ n) (hn46 : n ≤ 46)
    (hcontinue :
      (CPOW_PRECISION : ℝ) <
        firstTerm * (1 / 2 : ℝ) ^ (n - 2) +
          (3 * ((n - 1 : ℕ) : ℝ) - 2)) :
    accumulatedError n < TENTH_MIN_FEE_RATE * firstTerm := by
  interval_cases n <;>
    norm_num [accumulatedError, TENTH_MIN_FEE_RATE, MIN_FEE_RATE,
      MIN_FEE, STROOP, CPOW_PRECISION] at hcontinue ⊢ <;>
    linarith

/--
With the exact-input contraction factor `1/4`, the sign-specific first-term
floor fact tightens the certified fee share from ten percent to five percent.
-/
theorem accumulated_error_lt_five_percent_min_fee_of_multiterm
    {n : ℕ} {firstTerm : ℝ}
    (hn2 : 2 ≤ n) (hn46 : n ≤ 46)
    (hfirstIfSecond : n = 2 → (CPOW_PRECISION : ℝ) < firstTerm)
    (hcontinue :
      (CPOW_PRECISION : ℝ) <
        firstTerm * (1 / 4 : ℝ) ^ (n - 2) +
          (3 * ((n - 1 : ℕ) : ℝ) - 2)) :
    accumulatedError n < FIVE_PERCENT_MIN_FEE_RATE * firstTerm := by
  interval_cases n <;>
    norm_num [accumulatedError, FIVE_PERCENT_MIN_FEE_RATE, MIN_FEE_RATE,
      MIN_FEE, STROOP, CPOW_PRECISION] at hfirstIfSecond hcontinue ⊢ <;>
    linarith

/-- Exact fractional-binomial terms contract geometrically from term one. -/
theorem fractional_binomial_terms_from_first_bound
    (T : ℕ → ℝ) {a x q : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hx : |x| ≤ q)
    (hrec : ∀ n,
      T (n + 1) = T n * (a - (n : ℝ)) * x / ((n : ℝ) + 1)) :
    ∀ n, |T (n + 1)| ≤ |T 1| * q ^ n := by
  apply geometric_term_bound (M := fun n ↦ |T (n + 1)|)
    (S := |T 1|) (q := q) (le_refl _) (le_trans (abs_nonneg x) hx)
  intro n
  rw [hrec (n + 1)]
  simpa [Nat.cast_add, Nat.cast_one, add_assoc] using
    fractional_binomial_step_contracts
      (a := a) (x := x) (q := q) (term := T (n + 1)) ha0 ha1 hx (n + 1)

/-- Reaching a later iteration supplies the threshold premise used above. -/
theorem continued_loop_forces_first_term_scale
    (T : ℕ → ℝ) {a x previous : ℝ} {n : ℕ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hx0 : |x| ≤ 1 / 2)
    (hrec : ∀ k,
      T (k + 1) = T k * (a - (k : ℝ)) * x / ((k : ℝ) + 1))
    (hn2 : 2 ≤ n)
    (hprevious : (CPOW_PRECISION : ℝ) < |previous|)
    (herror :
      |T (n - 1) - previous| < 3 * ((n - 1 : ℕ) : ℝ) - 2) :
    (CPOW_PRECISION : ℝ) <
      |T 1| * (1 / 2 : ℝ) ^ (n - 2) +
        (3 * ((n - 1 : ℕ) : ℝ) - 2) := by
  have hterms := fractional_binomial_terms_from_first_bound
    T ha0 ha1 hx0 hrec (n - 2)
  have hindex : n - 2 + 1 = n - 1 := by omega
  rw [hindex] at hterms
  have hcomputed := computed_term_abs_lt herror
  linarith

/-- Exact-input bases contract terms by the sharper configured factor `1/4`. -/
theorem continued_exact_input_loop_forces_first_term_scale
    (T : ℕ → ℝ) {a x previous : ℝ} {n : ℕ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hx0 : |x| ≤ 1 / 4)
    (hrec : ∀ k,
      T (k + 1) = T k * (a - (k : ℝ)) * x / ((k : ℝ) + 1))
    (hn2 : 2 ≤ n)
    (hprevious : (CPOW_PRECISION : ℝ) < |previous|)
    (herror :
      |T (n - 1) - previous| < 3 * ((n - 1 : ℕ) : ℝ) - 2) :
    (CPOW_PRECISION : ℝ) <
      |T 1| * (1 / 4 : ℝ) ^ (n - 2) +
        (3 * ((n - 1 : ℕ) : ℝ) - 2) := by
  have hterms := fractional_binomial_terms_from_first_bound
    T ha0 ha1 hx0 hrec (n - 2)
  have hindex : n - 2 + 1 = n - 1 := by omega
  rw [hindex] at hterms
  have hcomputed := computed_term_abs_lt herror
  linarith

/--
If a negative exact first term is floored to an integer whose magnitude is
above an integer threshold, the exact magnitude is strictly above that same
threshold.
-/
theorem negative_floor_above_integer_threshold
    {rounded threshold : ℤ} {exact : ℝ}
    (hfloor : IsFloor rounded exact)
    (hexactNonpos : exact ≤ 0)
    (hrounded : (threshold : ℝ) < |(rounded : ℝ)|) :
    (threshold : ℝ) < |exact| := by
  have hroundedNonpos : (rounded : ℝ) ≤ 0 := le_trans hfloor.le hexactNonpos
  rw [abs_of_nonpos hroundedNonpos] at hrounded
  rw [abs_of_nonpos hexactNonpos]
  have hroundedInt : threshold < -rounded := by exact_mod_cast hrounded
  have hsuccessor : threshold + 1 ≤ -rounded := by omega
  have hsuccessorReal : (threshold : ℝ) + 1 ≤ (-rounded : ℤ) := by
    exact_mod_cast hsuccessor
  push_cast at hsuccessorReal
  linarith [hfloor.lt_add_one]

/-- The configured minimum fee keeps the maximum adjusted input ratio below one third. -/
theorem configured_min_fee_adjusted_input_ratio_lt_one_third :
    (1 - MIN_FEE_RATE) * ((MAX_IN_RATIO : ℝ) / STROOP) < 1 / 3 := by
  norm_num [MIN_FEE_RATE, MIN_FEE, MAX_IN_RATIO, STROOP]

/-- A minimum-fee exact-input swap has `abs(base - 1) < 1/4`. -/
theorem configured_exact_input_base_displacement_lt_one_fourth
    {computedBase adjustedRatio : ℝ}
    (hadjusted0 : 0 ≤ adjustedRatio)
    (hadjustedMax :
      adjustedRatio ≤
        (1 - MIN_FEE_RATE) * ((MAX_IN_RATIO : ℝ) / STROOP))
    (hceil : 1 / (1 + adjustedRatio) ≤ computedBase)
    (hbaseUpper : computedBase ≤ 1) :
    |computedBase - 1| < 1 / 4 := by
  have hadjustedThird : adjustedRatio < 1 / 3 :=
    lt_of_le_of_lt hadjustedMax configured_min_fee_adjusted_input_ratio_lt_one_third
  have hdenom : 0 < 1 + adjustedRatio := by linarith
  have hratioQuarter : adjustedRatio / (1 + adjustedRatio) < 1 / 4 := by
    apply (div_lt_iff₀ hdenom).2
    linarith
  have hid : 1 - 1 / (1 + adjustedRatio) =
      adjustedRatio / (1 + adjustedRatio) := by
    field_simp
  have hdisplacement : 1 - computedBase < 1 / 4 := by
    calc
      1 - computedBase ≤ 1 - 1 / (1 + adjustedRatio) := by linarith
      _ = adjustedRatio / (1 + adjustedRatio) := hid
      _ < 1 / 4 := hratioQuarter
  rw [abs_of_nonpos (sub_nonpos.mpr hbaseUpper)]
  linarith

/--
On the below-one path, the exact infinite sum is no greater than its finite
partial sum. Consequently, only accumulated fixed-point error can put the
computed sum below the exact power; the omitted tail cannot worsen the
adverse error.
-/
theorem monotone_partial_sum_adverse_error_lt
    {exactPower exactPartial computedPartial error : ℝ}
    (hpower : exactPower ≤ exactPartial)
    (hsum : |exactPartial - computedPartial| < error) :
    exactPower - computedPartial < error := by
  have hpartial : exactPartial - computedPartial < error :=
    lt_of_le_of_lt (le_abs_self (exactPartial - computedPartial)) hsum
  linarith

/-- The baseline one-term `+1` correction is conservative on this path. -/
theorem first_term_upper_has_no_adverse_error
    {exactPower exactPartial computedPartial : ℝ}
    (hpower : exactPower ≤ exactPartial)
    (hfloor : exactPartial < computedPartial + 1) :
    exactPower ≤ computedPartial + 1 :=
  le_trans hpower (le_of_lt hfloor)

/--
The computed exact-input base displacement cannot exceed the nominal input to
balance ratio. This connects the first binomial term to the input amount on
which the swap fee is charged.
-/
theorem exact_input_base_displacement_le_nominal_ratio
    {computedBase adjustedRatio nominalRatio : ℝ}
    (hadjusted0 : 0 ≤ adjustedRatio)
    (hadjustedNominal : adjustedRatio ≤ nominalRatio)
    (hceil : 1 / (1 + adjustedRatio) ≤ computedBase) :
    1 - computedBase ≤ nominalRatio := by
  have hdenom : 0 < 1 + adjustedRatio := by linarith
  have hratio : adjustedRatio / (1 + adjustedRatio) ≤ adjustedRatio := by
    apply (div_le_iff₀ hdenom).2
    nlinarith [sq_nonneg adjustedRatio]
  have hid : 1 - 1 / (1 + adjustedRatio) =
      adjustedRatio / (1 + adjustedRatio) := by
    field_simp
  calc
    1 - computedBase ≤ 1 - 1 / (1 + adjustedRatio) := by linarith
    _ = adjustedRatio / (1 + adjustedRatio) := hid
    _ ≤ adjustedRatio := hratio
    _ ≤ nominalRatio := hadjustedNominal

/-- The minimum fee's spot-normalized output value dominates its first-term scale. -/
theorem minimum_fee_value_dominates_first_term
    {S a fullExponent q nominalRatio firstTerm feeValue : ℝ}
    (hS0 : 0 ≤ S) (ha0 : 0 ≤ a)
    (haFull : a ≤ fullExponent) (hnominal0 : 0 ≤ nominalRatio)
    (hqNominal : q ≤ nominalRatio)
    (hfirst : firstTerm = S * a * q)
    (hfee : feeValue = MIN_FEE_RATE * (S * fullExponent * nominalRatio)) :
    TENTH_MIN_FEE_RATE * firstTerm ≤ feeValue / 10 := by
  have hSa0 : 0 ≤ S * a := mul_nonneg hS0 ha0
  have hdisplacement : S * a * q ≤ S * a * nominalRatio :=
    mul_le_mul_of_nonneg_left hqNominal hSa0
  have hscale0 : 0 ≤ S * nominalRatio := mul_nonneg hS0 hnominal0
  have hexponent : S * a * nominalRatio ≤ S * fullExponent * nominalRatio := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left haFull hscale0
  have hterm : S * a * q ≤ S * fullExponent * nominalRatio :=
    le_trans hdisplacement hexponent
  calc
    TENTH_MIN_FEE_RATE * firstTerm =
        (1 / 10000000 : ℝ) * (S * a * q) := by
      rw [hfirst, tenth_minimum_fee_rate_value]
    _ ≤ (1 / 10000000 : ℝ) * (S * fullExponent * nominalRatio) :=
      mul_le_mul_of_nonneg_left hterm (by norm_num)
    _ = feeValue / 10 := by
      rw [hfee, minimum_fee_rate_value]
      ring

/-- The same first-term comparison specialized to five percent of fee value. -/
theorem five_percent_minimum_fee_value_dominates_first_term
    {S a fullExponent q nominalRatio firstTerm feeValue : ℝ}
    (hS0 : 0 ≤ S) (ha0 : 0 ≤ a)
    (haFull : a ≤ fullExponent) (hnominal0 : 0 ≤ nominalRatio)
    (hqNominal : q ≤ nominalRatio)
    (hfirst : firstTerm = S * a * q)
    (hfee : feeValue = MIN_FEE_RATE * (S * fullExponent * nominalRatio)) :
    FIVE_PERCENT_MIN_FEE_RATE * firstTerm ≤ feeValue / 20 := by
  have hSa0 : 0 ≤ S * a := mul_nonneg hS0 ha0
  have hdisplacement : S * a * q ≤ S * a * nominalRatio :=
    mul_le_mul_of_nonneg_left hqNominal hSa0
  have hscale0 : 0 ≤ S * nominalRatio := mul_nonneg hS0 hnominal0
  have hexponent : S * a * nominalRatio ≤ S * fullExponent * nominalRatio := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left haFull hscale0
  have hterm : S * a * q ≤ S * fullExponent * nominalRatio :=
    le_trans hdisplacement hexponent
  calc
    FIVE_PERCENT_MIN_FEE_RATE * firstTerm =
        (1 / 20000000 : ℝ) * (S * a * q) := by
      rw [hfirst, five_percent_minimum_fee_rate_value]
    _ ≤ (1 / 20000000 : ℝ) * (S * fullExponent * nominalRatio) :=
      mul_le_mul_of_nonneg_left hterm (by norm_num)
    _ = feeValue / 20 := by
      rw [hfee, minimum_fee_rate_value]
      ring

/--
Abstract end-to-end comparison for a multi-term baseline fractional result.
All quantities are normalized to raw `BONE`-scaled output value. Under the
exact-input path premises, adverse approximation error is less than ten
percent of the minimum fee value.
-/
theorem baseline_multiterm_adverse_error_lt_tenth_min_fee
    {n : ℕ} {firstTerm exactPower exactPartial computedPartial feeValue : ℝ}
    (hn2 : 2 ≤ n) (hn46 : n ≤ 46)
    (hcontinue :
      (CPOW_PRECISION : ℝ) <
        firstTerm * (1 / 2 : ℝ) ^ (n - 2) +
          (3 * ((n - 1 : ℕ) : ℝ) - 2))
    (hpower : exactPower ≤ exactPartial)
    (hsum : |exactPartial - computedPartial| < accumulatedError n)
    (hfee : TENTH_MIN_FEE_RATE * firstTerm ≤ feeValue / 10) :
    exactPower - computedPartial < feeValue / 10 := by
  have hadverse := monotone_partial_sum_adverse_error_lt hpower hsum
  have hbudget := accumulated_error_lt_tenth_min_fee_of_multiterm
    hn2 hn46 hcontinue
  linarith

/--
Composition of the recurrence, continuation, fee-scale, and adverse-error
lemmas for the multi-term exact-input fractional path.
-/
theorem baseline_exact_input_multiterm_adverse_error_lt_tenth_min_fee
    (T : ℕ → ℝ)
    {n : ℕ} {a fullExponent x previous q nominalRatio : ℝ}
    {exactPower exactPartial computedPartial feeValue : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hx : |x| ≤ 1 / 2)
    (hrec : ∀ k,
      T (k + 1) = T k * (a - (k : ℝ)) * x / ((k : ℝ) + 1))
    (hn2 : 2 ≤ n) (hn46 : n ≤ 46)
    (hprevious : (CPOW_PRECISION : ℝ) < |previous|)
    (htermError :
      |T (n - 1) - previous| < 3 * ((n - 1 : ℕ) : ℝ) - 2)
    (hfirst : |T 1| = (BONE : ℝ) * a * q)
    (haFull : a ≤ fullExponent) (hnominal0 : 0 ≤ nominalRatio)
    (hqNominal : q ≤ nominalRatio)
    (hfeeValue :
      feeValue = MIN_FEE_RATE * ((BONE : ℝ) * fullExponent * nominalRatio))
    (hpower : exactPower ≤ exactPartial)
    (hsum : |exactPartial - computedPartial| < accumulatedError n) :
    exactPower - computedPartial < feeValue / 10 := by
  have hcontinue := continued_loop_forces_first_term_scale
    T ha0 ha1 hx hrec hn2 hprevious htermError
  have hfee := minimum_fee_value_dominates_first_term
    (S := (BONE : ℝ)) (a := a) (fullExponent := fullExponent)
    (q := q) (nominalRatio := nominalRatio)
    (firstTerm := |T 1|) (feeValue := feeValue)
    (by norm_num [BONE]) ha0 haFull hnominal0 hqNominal hfirst hfeeValue
  exact baseline_multiterm_adverse_error_lt_tenth_min_fee
    hn2 hn46 hcontinue hpower hsum hfee

/--
The sharper exact-input theorem: adverse multi-term fractional approximation
error is strictly below five percent of the minimum fee's spot-normalized
value.
-/
theorem baseline_exact_input_multiterm_adverse_error_lt_five_percent_min_fee
    (T : ℕ → ℝ)
    {n : ℕ} {a fullExponent x previous q nominalRatio : ℝ}
    {firstRounded : ℤ}
    {exactPower exactPartial computedPartial feeValue : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hx : |x| ≤ 1 / 4)
    (hrec : ∀ k,
      T (k + 1) = T k * (a - (k : ℝ)) * x / ((k : ℝ) + 1))
    (hn2 : 2 ≤ n) (hn46 : n ≤ 46)
    (hprevious : (CPOW_PRECISION : ℝ) < |previous|)
    (htermError :
      |T (n - 1) - previous| < 3 * ((n - 1 : ℕ) : ℝ) - 2)
    (hfirstPrevious : n = 2 → previous = (firstRounded : ℝ))
    (hfirstFloor : IsFloor firstRounded (T 1))
    (hfirstNonpos : T 1 ≤ 0)
    (hfirst : |T 1| = (BONE : ℝ) * a * q)
    (haFull : a ≤ fullExponent) (hnominal0 : 0 ≤ nominalRatio)
    (hqNominal : q ≤ nominalRatio)
    (hfeeValue :
      feeValue = MIN_FEE_RATE * ((BONE : ℝ) * fullExponent * nominalRatio))
    (hpower : exactPower ≤ exactPartial)
    (hsum : |exactPartial - computedPartial| < accumulatedError n) :
    exactPower - computedPartial < feeValue / 20 := by
  have hcontinue := continued_exact_input_loop_forces_first_term_scale
    T ha0 ha1 hx hrec hn2 hprevious htermError
  have hfirstIfSecond : n = 2 → (CPOW_PRECISION : ℝ) < |T 1| := by
    intro hn
    have hprevFirst := hfirstPrevious hn
    rw [hprevFirst] at hprevious
    exact negative_floor_above_integer_threshold
      hfirstFloor hfirstNonpos (by simpa [CPOW_PRECISION] using hprevious)
  have hbudget := accumulated_error_lt_five_percent_min_fee_of_multiterm
    hn2 hn46 hfirstIfSecond hcontinue
  have hadverse := monotone_partial_sum_adverse_error_lt hpower hsum
  have hfee := five_percent_minimum_fee_value_dominates_first_term
    (S := (BONE : ℝ)) (a := a) (fullExponent := fullExponent)
    (q := q) (nominalRatio := nominalRatio)
    (firstTerm := |T 1|) (feeValue := feeValue)
    (by norm_num [BONE]) ha0 haFull hnominal0 hqNominal hfirst hfeeValue
  linarith

/--
For a one-term exact-input approximation, the baseline's one-unit upper
correction has no adverse error. It is therefore strictly below any positive
percentage of a positive fee value.
-/
theorem baseline_exact_input_first_term_adverse_error_lt_tenth_min_fee
    {exactPower exactPartial computedPartial feeValue : ℝ}
    (hpower : exactPower ≤ exactPartial)
    (hfloor : exactPartial < computedPartial + 1)
    (hfeePositive : 0 < feeValue) :
    exactPower - (computedPartial + 1) < feeValue / 10 := by
  have hconservative := first_term_upper_has_no_adverse_error hpower hfloor
  linarith

/--
For a below-one base, an upper-rounded integer factor in `[0, 1]` cannot
amplify an adverse fractional-factor error. An upper-rounded final product can
only improve the result further.
-/
theorem below_one_upper_composition_preserves_adverse_bound
    {wholeExact wholeComputed fracExact fracComputed composed error : ℝ}
    (hwhole0 : 0 ≤ wholeExact) (hwhole1 : wholeExact ≤ 1)
    (hfracComputed0 : 0 ≤ fracComputed)
    (hwholeUpper : wholeExact ≤ wholeComputed)
    (hcomposedUpper : wholeComputed * fracComputed ≤ composed)
    (herror0 : 0 < error)
    (hfracError : fracExact - fracComputed < error) :
    wholeExact * fracExact - composed < error := by
  have hproduct : wholeExact * fracComputed ≤ composed := by
    calc
      wholeExact * fracComputed ≤ wholeComputed * fracComputed :=
        mul_le_mul_of_nonneg_right hwholeUpper hfracComputed0
      _ ≤ composed := hcomposedUpper
  have hreduce :
      wholeExact * fracExact - composed ≤
        wholeExact * (fracExact - fracComputed) := by
    linarith
  by_cases hdelta : 0 ≤ fracExact - fracComputed
  · have hscale :
        wholeExact * (fracExact - fracComputed) ≤
          fracExact - fracComputed :=
      mul_le_of_le_one_left hdelta hwhole1
    linarith
  · have hscale : wholeExact * (fracExact - fracComputed) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hwhole0 (le_of_not_ge hdelta)
    linarith

/-- A positive output-balance scale preserves the fee comparison. -/
theorem positive_output_scale_preserves_fee_comparison
    {adverse feeValue outputScale : ℝ}
    (hscale : 0 < outputScale)
    (herror : adverse < feeValue / 10) :
    outputScale * adverse < outputScale * feeValue / 10 := by
  have := mul_lt_mul_of_pos_left herror hscale
  linarith

end CometCPow
