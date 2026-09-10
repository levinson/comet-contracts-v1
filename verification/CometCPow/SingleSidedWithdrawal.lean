import CometCPow.ExactInputSwap
import CometCPow.OperationFeeBound

namespace CometCPow

/-!
Operation-level model for `wdr_tokn_amt_in_get_lp_tokns_out`, the
single-sided withdrawal that burns an exact LP-token amount and returns one
underlying token.  Its `c_pow` path has a below-one base, a floored reciprocal
weight exponent, and `round_up = true`.
-/

/-- The ideal remaining-pool-supply ratio after burning LP tokens. -/
noncomputable def singleSidedWithdrawalIdealBase (nominalRatio : ℝ) : ℝ :=
  1 - nominalRatio

/-- The exact weighted fee charged to a single-sided withdrawal. -/
noncomputable def singleSidedWithdrawalFeeRate (weight feeRate : ℝ) : ℝ :=
  (1 - weight) * feeRate

/-- Exact token output in the output balance's unit. -/
noncomputable def singleSidedWithdrawalIdealOutput
    (outputBalance weight feeRate nominalRatio : ℝ) : ℝ :=
  outputBalance *
    (1 - singleSidedWithdrawalIdealBase nominalRatio ^ (1 / weight)) *
      (1 - singleSidedWithdrawalFeeRate weight feeRate)

/-- Minimum weighted-fee spot value in raw `c_pow` units. -/
noncomputable def singleSidedWithdrawalMinimumFeePowerValue
    (weight nominalRatio : ℝ) : ℝ :=
  MIN_FEE_RATE *
    ((BONE : ℝ) * ((1 - weight) / weight) * nominalRatio)

/-- Minimum weighted-fee spot value in the output token's unit. -/
noncomputable def singleSidedWithdrawalMinimumFeeOutputValue
    (outputBalance weight nominalRatio : ℝ) : ℝ :=
  MIN_FEE_RATE *
    (outputBalance * ((1 - weight) / weight) * nominalRatio)

/-- The pool-ratio ceiling lies between the ideal remaining ratio and one. -/
theorem single_sided_withdrawal_base_ceil_refines
    {nominalRatio computedBase : ℝ} {computedBaseRaw : ℤ}
    (hratio0 : 0 ≤ nominalRatio)
    (hcomputedBase : computedBase = (computedBaseRaw : ℝ) / BONE)
    (hbaseCeil :
      IsCeil computedBaseRaw ((BONE : ℝ) * (1 - nominalRatio))) :
    singleSidedWithdrawalIdealBase nominalRatio ≤ computedBase ∧
      computedBase ≤ 1 := by
  have hB : (0 : ℝ) < BONE := by norm_num [BONE]
  have hexactUpper :
      (BONE : ℝ) * (1 - nominalRatio) ≤ (BONE : ℝ) := by
    have hbaseUpper : 1 - nominalRatio ≤ 1 := by linarith
    simpa using mul_le_mul_of_nonneg_left hbaseUpper hB.le
  have hrawUpper : computedBaseRaw ≤ (BONE : ℤ) :=
    hbaseCeil.le_integer_upper (by exact_mod_cast hexactUpper)
  constructor
  · rw [singleSidedWithdrawalIdealBase, hcomputedBase]
    exact hbaseCeil.le_normalized hB
  · rw [hcomputedBase]
    exact (div_le_one hB).2 (by exact_mod_cast hrawUpper)

/-- Flooring the reciprocal weight gives a non-negative exponent no larger than ideal. -/
theorem single_sided_withdrawal_exponent_floor_refines
    {weight computedExponent : ℝ} {computedExponentRaw : ℤ}
    (hraw0 : 0 ≤ computedExponentRaw)
    (hcomputedExponent :
      computedExponent = (computedExponentRaw : ℝ) / BONE)
    (hexponentFloor :
      IsFloor computedExponentRaw ((BONE : ℝ) * (1 / weight))) :
    0 ≤ computedExponent ∧ computedExponent ≤ 1 / weight := by
  have hB : (0 : ℝ) < BONE := by norm_num [BONE]
  constructor
  · rw [hcomputedExponent]
    positivity
  · rw [hcomputedExponent]
    exact hexponentFloor.normalized_le hB

/-- Base ceiling and reciprocal-exponent floor both increase a below-one power. -/
theorem single_sided_withdrawal_rounded_power_dominates_ideal
    {nominalRatio weight computedBase computedExponent : ℝ}
    (hratio0 : 0 ≤ nominalRatio) (hratio1 : nominalRatio < 1)
    (hbase : singleSidedWithdrawalIdealBase nominalRatio ≤ computedBase)
    (hcomputedExponent0 : 0 ≤ computedExponent)
    (hexponentFloor : computedExponent ≤ 1 / weight) :
    singleSidedWithdrawalIdealBase nominalRatio ^ (1 / weight) ≤
      computedBase ^ computedExponent := by
  have hidealBase0 : 0 < singleSidedWithdrawalIdealBase nominalRatio := by
    rw [singleSidedWithdrawalIdealBase]
    linarith
  have hidealBase1 : singleSidedWithdrawalIdealBase nominalRatio ≤ 1 := by
    rw [singleSidedWithdrawalIdealBase]
    linarith
  calc
    singleSidedWithdrawalIdealBase nominalRatio ^ (1 / weight) ≤
        singleSidedWithdrawalIdealBase nominalRatio ^ computedExponent :=
      Real.rpow_le_rpow_of_exponent_ge
        hidealBase0 hidealBase1 hexponentFloor
    _ ≤ computedBase ^ computedExponent :=
      Real.rpow_le_rpow hidealBase0.le hbase hcomputedExponent0

/-- The weighted fee multiplier lies in `[0,1]` on the configured domain. -/
theorem single_sided_withdrawal_fee_multiplier_bounds
    {weight feeRate : ℝ}
    (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1)
    (hfee0 : 0 ≤ feeRate) (hfee1 : feeRate ≤ 1) :
    0 ≤ 1 - singleSidedWithdrawalFeeRate weight feeRate ∧
      1 - singleSidedWithdrawalFeeRate weight feeRate ≤ 1 := by
  rw [singleSidedWithdrawalFeeRate]
  have hweighted0 : 0 ≤ (1 - weight) * feeRate :=
    mul_nonneg (sub_nonneg.mpr hweight1) hfee0
  have hweighted1 : (1 - weight) * feeRate ≤ 1 := by
    have hfactor : (1 - weight) * feeRate ≤ 1 * 1 :=
      mul_le_mul (by linarith) hfee1 hfee0 (by norm_num)
    simpa using hfactor
  constructor <;> linarith

/-- Two caller floors and the new-balance ceiling cannot increase token output. -/
theorem single_sided_withdrawal_output_floor_chain
    {newBalance tokenAmountBeforeFee result output : ℤ}
    {outputBalance computedPower feeMultiplier scale : ℝ}
    (hfeeMultiplier0 : 0 ≤ feeMultiplier) (hscale : 0 < scale)
    (hnewBalanceCeil :
      IsCeil newBalance (outputBalance * (computedPower / (BONE : ℝ))))
    (htokenAmount :
      (tokenAmountBeforeFee : ℝ) = outputBalance - (newBalance : ℝ))
    (hfeeFloor :
      IsFloor result ((tokenAmountBeforeFee : ℝ) * feeMultiplier))
    (hdownscaleFloor : IsFloor output ((result : ℝ) / scale)) :
    (output : ℝ) ≤
      outputBalance / scale * (1 - computedPower / (BONE : ℝ)) *
        feeMultiplier := by
  have htokenUpper :
      (tokenAmountBeforeFee : ℝ) ≤
        outputBalance * (1 - computedPower / (BONE : ℝ)) := by
    rw [htokenAmount]
    have hnew := hnewBalanceCeil.le
    linarith
  have hfeeUpper :
      (result : ℝ) ≤
        outputBalance * (1 - computedPower / (BONE : ℝ)) * feeMultiplier :=
    le_trans hfeeFloor.le
      (mul_le_mul_of_nonneg_right htokenUpper hfeeMultiplier0)
  have hscaled := (div_le_div_iff_of_pos_right hscale).2 hfeeUpper
  calc
    (output : ℝ) ≤ (result : ℝ) / scale := hdownscaleFloor.le
    _ ≤
        (outputBalance * (1 - computedPower / (BONE : ℝ)) * feeMultiplier) /
          scale := hscaled
    _ = outputBalance / scale * (1 - computedPower / (BONE : ℝ)) *
          feeMultiplier := by ring

/-- Scaling an adverse power bound by a multiplier in `[0,1]` preserves it. -/
theorem nonnegative_multiplier_preserves_positive_upper_bound
    {value multiplier upper : ℝ}
    (hmultiplier0 : 0 ≤ multiplier) (hmultiplier1 : multiplier ≤ 1)
    (hupper0 : 0 < upper) (hvalue : value < upper) :
    multiplier * value < upper := by
  by_cases hvalue0 : 0 ≤ value
  · have hscaled : multiplier * value ≤ 1 * value :=
      mul_le_mul_of_nonneg_right hmultiplier1 hvalue0
    linarith
  · have hnegative : multiplier * value ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hmultiplier0 (le_of_not_ge hvalue0)
    linarith

/--
Compose the below-one power bound with the exact weighted fee and every
directional rounding operation in the public withdrawal calculation.
-/
theorem single_sided_withdrawal_adverse_error_lt_five_percent_min_fee
    {outputBalance weight feeRate nominalRatio computedBase computedExponent
      computedPower computedOutput scale : ℝ}
    (houtputBalance : 0 < outputBalance) (hscale : 0 < scale)
    (hweight0 : 0 < weight) (hweight1 : weight < 1)
    (hfee0 : 0 ≤ feeRate) (hfee1 : feeRate ≤ 1)
    (hratio0 : 0 ≤ nominalRatio) (hratioPositive : 0 < nominalRatio)
    (hratio1 : nominalRatio < 1)
    (hbase : singleSidedWithdrawalIdealBase nominalRatio ≤ computedBase)
    (hcomputedExponent0 : 0 ≤ computedExponent)
    (hexponentFloor : computedExponent ≤ 1 / weight)
    (hcpow :
      (BONE : ℝ) * computedBase ^ computedExponent - computedPower <
        singleSidedWithdrawalMinimumFeePowerValue weight nominalRatio / 20)
    (hcomputedOutput :
      computedOutput ≤ outputBalance / scale *
        (1 - computedPower / (BONE : ℝ)) *
          (1 - singleSidedWithdrawalFeeRate weight feeRate)) :
    computedOutput -
        singleSidedWithdrawalIdealOutput
          (outputBalance / scale) weight feeRate nominalRatio <
      singleSidedWithdrawalMinimumFeeOutputValue
        (outputBalance / scale) weight nominalRatio / 20 := by
  have hB : (0 : ℝ) < BONE := by norm_num [BONE]
  have hfeeBounds := single_sided_withdrawal_fee_multiplier_bounds
    hweight0.le hweight1.le hfee0 hfee1
  have hpowerDirection := single_sided_withdrawal_rounded_power_dominates_ideal
    hratio0 hratio1 hbase hcomputedExponent0 hexponentFloor
  have hrawDirection :
      (BONE : ℝ) *
          singleSidedWithdrawalIdealBase nominalRatio ^ (1 / weight) ≤
        (BONE : ℝ) * computedBase ^ computedExponent :=
    mul_le_mul_of_nonneg_left hpowerDirection hB.le
  have hadversePower :
      (BONE : ℝ) *
          singleSidedWithdrawalIdealBase nominalRatio ^ (1 / weight) -
        computedPower <
      singleSidedWithdrawalMinimumFeePowerValue weight nominalRatio / 20 := by
    linarith
  have hfeePowerPositive :
      0 < singleSidedWithdrawalMinimumFeePowerValue weight nominalRatio := by
    rw [singleSidedWithdrawalMinimumFeePowerValue, minimum_fee_rate_value]
    have hfeeExponent : 0 < (1 - weight) / weight := div_pos (by linarith) hweight0
    exact mul_pos (by norm_num)
      (mul_pos (mul_pos (by norm_num [BONE]) hfeeExponent)
        hratioPositive)
  have hscaledByFee := nonnegative_multiplier_preserves_positive_upper_bound
    hfeeBounds.1 hfeeBounds.2 (div_pos hfeePowerPositive (by norm_num))
      hadversePower
  have hcallerScale : 0 < outputBalance / scale / (BONE : ℝ) :=
    div_pos (div_pos houtputBalance hscale) hB
  have hscaled := mul_lt_mul_of_pos_left hscaledByFee hcallerScale
  calc
    computedOutput -
          singleSidedWithdrawalIdealOutput
            (outputBalance / scale) weight feeRate nominalRatio ≤
        outputBalance / scale * (1 - computedPower / (BONE : ℝ)) *
            (1 - singleSidedWithdrawalFeeRate weight feeRate) -
          singleSidedWithdrawalIdealOutput
            (outputBalance / scale) weight feeRate nominalRatio :=
      sub_le_sub_right hcomputedOutput _
    _ = (outputBalance / scale / (BONE : ℝ)) *
        (1 - singleSidedWithdrawalFeeRate weight feeRate) *
          ((BONE : ℝ) *
              singleSidedWithdrawalIdealBase nominalRatio ^ (1 / weight) -
            computedPower) := by
      rw [singleSidedWithdrawalIdealOutput]
      field_simp [ne_of_gt hB, ne_of_gt hscale]
      ring
    _ = (outputBalance / scale / (BONE : ℝ)) *
        ((1 - singleSidedWithdrawalFeeRate weight feeRate) *
          ((BONE : ℝ) *
              singleSidedWithdrawalIdealBase nominalRatio ^ (1 / weight) -
            computedPower)) := by ring
    _ < (outputBalance / scale / (BONE : ℝ)) *
        (singleSidedWithdrawalMinimumFeePowerValue weight nominalRatio / 20) := hscaled
    _ = singleSidedWithdrawalMinimumFeeOutputValue
          (outputBalance / scale) weight nominalRatio / 20 := by
      rw [singleSidedWithdrawalMinimumFeePowerValue,
        singleSidedWithdrawalMinimumFeeOutputValue]
      field_simp [ne_of_gt hB, ne_of_gt hscale, ne_of_gt hweight0]
      ring

/-- Instantiate the operation theorem from the fixed-point caller refinements. -/
theorem single_sided_withdrawal_from_fixed_point_refinements
    {poolSupply poolAmountIn nominalRatio outputBalance weight feeRate
      computedBase computedExponent computedPower feeMultiplier scale : ℝ}
    {computedBaseRaw computedExponentRaw newBalance tokenAmountBeforeFee
      result output : ℤ}
    (hpoolSupply : 0 < poolSupply) (hpoolAmountIn : 0 < poolAmountIn)
    (hnominal : nominalRatio = poolAmountIn / poolSupply)
    (hratio1 : nominalRatio < 1)
    (houtputBalance : 0 < outputBalance)
    (hweight0 : 0 < weight) (hweight1 : weight < 1)
    (hfee0 : 0 ≤ feeRate) (hfee1 : feeRate ≤ 1)
    (hcomputedBase : computedBase = (computedBaseRaw : ℝ) / BONE)
    (hbaseCeil :
      IsCeil computedBaseRaw ((BONE : ℝ) * (1 - nominalRatio)))
    (hcomputedExponentRaw0 : 0 ≤ computedExponentRaw)
    (hcomputedExponent :
      computedExponent = (computedExponentRaw : ℝ) / BONE)
    (hexponentFloor :
      IsFloor computedExponentRaw ((BONE : ℝ) * (1 / weight)))
    (hcpow :
      (BONE : ℝ) * computedBase ^ computedExponent - computedPower <
        singleSidedWithdrawalMinimumFeePowerValue weight nominalRatio / 20)
    (hfeeMultiplier :
      feeMultiplier = 1 - singleSidedWithdrawalFeeRate weight feeRate)
    (hscale : 0 < scale)
    (hnewBalanceCeil :
      IsCeil newBalance (outputBalance * (computedPower / (BONE : ℝ))))
    (htokenAmount :
      (tokenAmountBeforeFee : ℝ) = outputBalance - (newBalance : ℝ))
    (hfeeFloor :
      IsFloor result ((tokenAmountBeforeFee : ℝ) * feeMultiplier))
    (hdownscaleFloor : IsFloor output ((result : ℝ) / scale)) :
    (output : ℝ) -
        singleSidedWithdrawalIdealOutput
          (outputBalance / scale) weight feeRate nominalRatio <
      singleSidedWithdrawalMinimumFeeOutputValue
        (outputBalance / scale) weight nominalRatio / 20 := by
  have hratio0 : 0 ≤ nominalRatio := by rw [hnominal]; positivity
  have hbase := single_sided_withdrawal_base_ceil_refines
    hratio0 hcomputedBase hbaseCeil
  have hexponent := single_sided_withdrawal_exponent_floor_refines
    hcomputedExponentRaw0 hcomputedExponent hexponentFloor
  have hfeeBounds := single_sided_withdrawal_fee_multiplier_bounds
    hweight0.le hweight1.le hfee0 hfee1
  have houtput := single_sided_withdrawal_output_floor_chain
    (by rw [hfeeMultiplier]; exact hfeeBounds.1) hscale hnewBalanceCeil
      htokenAmount hfeeFloor hdownscaleFloor
  rw [hfeeMultiplier] at houtput
  exact single_sided_withdrawal_adverse_error_lt_five_percent_min_fee
    houtputBalance hscale hweight0 hweight1 hfee0 hfee1 hratio0
      (by rw [hnominal]; positivity) hratio1
      hbase.1 hexponent.1 hexponent.2 hcpow houtput

/-- The fractional part of a floored reciprocal exponent is paid for by the weighted fee. -/
theorem single_sided_withdrawal_fractional_le_fee_exponent
    {integerPart : ℕ} {weight a computedExponent : ℝ}
    (hweight : 0 < weight) (hintegerPart : 1 ≤ integerPart)
    (hcomputedExponentSplit : computedExponent = (integerPart : ℝ) + a)
    (hcomputedExponentUpper : computedExponent ≤ 1 / weight) :
    a ≤ (1 - weight) / weight := by
  have hintegerReal : (1 : ℝ) ≤ integerPart := by exact_mod_cast hintegerPart
  have hbound : a ≤ 1 / weight - 1 := by
    rw [hcomputedExponentSplit] at hcomputedExponentUpper
    linarith
  have hid : 1 / weight - 1 = (1 - weight) / weight := by
    field_simp
  rwa [hid] at hbound

/-- The rounded remaining-supply displacement cannot exceed the burned-supply ratio. -/
theorem single_sided_withdrawal_displacement_le_nominal_ratio
    {nominalRatio computedBase : ℝ}
    (hbase : singleSidedWithdrawalIdealBase nominalRatio ≤ computedBase) :
    1 - computedBase ≤ nominalRatio := by
  rw [singleSidedWithdrawalIdealBase] at hbase
  linarith

/-- The closed-form recurrence budget is at most `3151` through iteration 46. -/
theorem single_sided_withdrawal_accumulated_error_le_3151
    {n : ℕ} (hn : n ≤ 46) : accumulatedError n ≤ 3151 := by
  have hnReal : (n : ℝ) ≤ 46 := by exact_mod_cast hn
  have hsecond : 0 ≤ 3 * (46 + (n : ℝ)) - 1 := by
    nlinarith [show (0 : ℝ) ≤ n by positivity]
  have hgap := mul_nonneg (sub_nonneg.mpr hnReal) hsecond
  rw [accumulatedError]
  nlinarith only [hgap]

/--
Concrete multi-term `c_pow` verification for the below-one reciprocal path.
The second stop uses its sign-specific five-unit bound; later stops use the
sharp second-term continuation estimate.  In both cases the below-one whole
power cannot amplify adverse fractional error.
-/
theorem baseline_single_sided_withdrawal_cpow_multiterm_adverse_error_lt_five_percent_min_fee
    (coefficientProduct multiplied computedTerm : ℕ → ℤ)
    {n integerPart : ℕ}
    {weight nominalRatio computedBase computedExponent a computedFractional
      wholeComputed computedPower : ℝ}
    {firstRounded computedPowerRaw : ℤ}
    (hweight0 : 0 < weight) (hweight1 : weight < 1)
    (hnominal0 : 0 ≤ nominalRatio) (hnominalPositive : 0 < nominalRatio)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hintegerPart : 1 ≤ integerPart)
    (hcomputedExponentSplit : computedExponent = (integerPart : ℝ) + a)
    (hcomputedExponentUpper : computedExponent ≤ 1 / weight)
    (hbaseLower : 1 / 2 ≤ computedBase)
    (hbaseUpper : computedBase ≤ 1) (hbaseNonunit : computedBase < 1)
    (hdisplacement : 1 - computedBase ≤ nominalRatio)
    (hn2 : 2 ≤ n)
    (hcontinued : ∀ k, 1 ≤ k → k < n →
      (CPOW_PRECISION : ℝ) < |(computedTerm k : ℝ)|)
    (hfirstFloor :
      IsFloor firstRounded (exactInputBinomialTerm a computedBase 1))
    (hfirstRounded : firstRounded = computedTerm 1)
    (hcoefficientFloor : ∀ k, 1 ≤ k → k < 50 →
      IsFloor (coefficientProduct (k + 1))
        ((BONE : ℝ) * (a - (k : ℝ)) * (computedBase - 1)))
    (hmultiplyTermFloor : ∀ k, 1 ≤ k → k < 50 →
      IsFloor (multiplied (k + 1))
        ((computedTerm k : ℝ) * (coefficientProduct (k + 1) : ℝ) /
          (BONE : ℝ)))
    (hdivideTermFloor : ∀ k, 1 ≤ k → k < 50 →
      IsFloor (computedTerm (k + 1))
        ((multiplied (k + 1) : ℝ) / ((k : ℝ) + 1)))
    (hcomputedFractional :
      computedFractional = (BONE : ℝ) +
        ∑ k ∈ Finset.range n, (computedTerm (k + 1) : ℝ))
    (hwholeTrace : UpperCPowiTrace computedBase integerPart wholeComputed)
    (hcomputedPower : computedPower = (computedPowerRaw : ℝ))
    (hcomposedCeil :
      IsCeil computedPowerRaw (wholeComputed * computedFractional)) :
    (BONE : ℝ) * computedBase ^ computedExponent - computedPower <
      singleSidedWithdrawalMinimumFeePowerValue weight nominalRatio / 20 := by
  let T : ℕ → ℝ := exactInputBinomialTerm a computedBase
  let U : ℕ → ℝ := fun k ↦ (computedTerm k : ℝ)
  let exactPartial : ℝ :=
    ∑ k ∈ Finset.range (n + 1), exactInputBinomialTerm a computedBase k
  have hbase0 : 0 < computedBase := lt_of_lt_of_le (by norm_num) hbaseLower
  have hxHalf : |computedBase - 1| ≤ (1 / 2 : ℝ) := by
    rw [abs_of_nonpos (sub_nonpos.mpr hbaseUpper)]
    linarith
  have hx : |computedBase - 1| ≤ (3 / 5 : ℝ) :=
    le_trans hxHalf (by norm_num)
  have hrec : ∀ k,
      T (k + 1) =
        T k * (a - (k : ℝ)) * (computedBase - 1) / ((k : ℝ) + 1) := by
    intro k
    exact exactInputBinomialTerm_succ a computedBase k
  have hfirstFacts := exactInputBinomialTerm_one ha0 hbaseUpper
  have hfirstNonpos : T 1 ≤ 0 := by
    change exactInputBinomialTerm a computedBase 1 ≤ 0
    rw [hfirstFacts.1]
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (by norm_num [BONE]) ha0) (sub_nonpos.mpr hbaseUpper)
  have hfirstMagnitude : |T 1| = (BONE : ℝ) * a * (1 - computedBase) :=
    hfirstFacts.2
  have hpartialUpper : (BONE : ℝ) * computedBase ^ a ≤ exactPartial := by
    exact exact_input_binomial_partial_upper ha0 ha1 hbase0 hbaseNonunit n
  have hexactPartial :
      exactPartial = (BONE : ℝ) + ∑ k ∈ Finset.range n, T (k + 1) := by
    dsimp [exactPartial, T]
    rw [Finset.sum_range_succ']
    simp
    ring
  have hfirstError : |T 1 - U 1| < 1 := by
    dsimp [T, U]
    rw [← hfirstRounded]
    exact hfirstFloor.abs_error_lt_one
  have hfirstBelowScale : |T 1| < BONE := by
    rw [hfirstMagnitude]
    have hproduct : a * (1 - computedBase) < 1 := by
      have hmul : a * (1 - computedBase) ≤ 1 * (1 - computedBase) :=
        mul_le_mul_of_nonneg_right ha1 (by linarith)
      linarith
    have hB : (0 : ℝ) < BONE := by norm_num [BONE]
    simpa only [mul_assoc, mul_one] using mul_lt_mul_of_pos_left hproduct hB
  have hexactTermMagnitude : ∀ k, 1 ≤ k → |T k| < BONE := by
    intro k hk
    have hterms := fractional_binomial_terms_from_first_bound
      T ha0 ha1 hxHalf hrec (k - 1)
    have hindex : k - 1 + 1 = k := by omega
    rw [hindex] at hterms
    have hpower1 : (1 / 2 : ℝ) ^ (k - 1) ≤ 1 :=
      pow_le_one₀ (by norm_num) (by norm_num)
    have hscale : |T 1| * (1 / 2 : ℝ) ^ (k - 1) ≤ |T 1| := by
      nlinarith [abs_nonneg (T 1)]
    exact lt_of_le_of_lt (le_trans hterms hscale) hfirstBelowScale
  have herrorRec : ∀ k, 1 ≤ k → k < 50 →
      |T (k + 1) - U (k + 1)| <
        (1 + 1 / (((k + 1 : ℕ) : ℝ) * (BONE : ℝ))) * |T k - U k| +
          1 / ((k + 1 : ℕ) : ℝ) + 1 / ((k + 1 : ℕ) : ℝ) + 1 := by
    intro k hk hk50
    have hcoefficientNonpos : a - (k : ℝ) ≤ 0 := by
      have hkReal : (1 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have hcoefficientBound : |a - (k : ℝ)| ≤ (k : ℝ) + 1 := by
      rw [abs_of_nonpos hcoefficientNonpos]
      linarith
    have hstep := three_floor_recurrence_step_error
      (S := (BONE : ℝ)) (K := (k : ℝ) + 1)
      (exactPrevious := T k) (computedPrevious := U k)
      (coefficient := a - (k : ℝ)) (displacement := computedBase - 1)
      (coefficientProduct := coefficientProduct (k + 1))
      (multiplied := multiplied (k + 1))
      (nextComputed := computedTerm (k + 1))
      (by norm_num [BONE]) (by positivity) hcoefficientBound
      (le_trans hxHalf (by norm_num)) (hexactTermMagnitude k hk)
      (hcoefficientFloor k hk hk50)
      (by simpa [U] using hmultiplyTermFloor k hk hk50)
      (hdivideTermFloor k hk hk50)
    rw [hrec k]
    simpa [U, Nat.cast_add, Nat.cast_one, add_assoc] using hstep
  have htermBounds := recurrence_error_budget (BONE : ℝ)
    (fun k ↦ |T k - U k|) (by norm_num [BONE]) hfirstError herrorRec
  have herror46 : |T 46 - U 46| < 3 * (46 : ℝ) - 2 :=
    htermBounds 46 (by norm_num) (by norm_num)
  have htermZero : |T 0| ≤ (BONE : ℝ) := by
    dsimp [T]
    simp
  have hstopsBy46 : |U 46| < (CPOW_PRECISION : ℝ) :=
    pool_operating_base_converges_by_iteration_46
      T ha0 ha1 hbaseLower (le_trans hbaseUpper (by norm_num))
        htermZero hrec herror46
  have hn46 : n ≤ 46 := by
    by_contra hn
    have hstillRunning := hcontinued 46 (by norm_num) (by omega)
    dsimp [U] at hstopsBy46
    linarith
  have hprevious : (CPOW_PRECISION : ℝ) < |U (n - 1)| := by
    simpa [U] using hcontinued (n - 1) (by omega) (by omega)
  have htermError :
      |T (n - 1) - U (n - 1)| < 3 * ((n - 1 : ℕ) : ℝ) - 2 :=
    htermBounds (n - 1) (by omega) (by omega)
  have hsumRaw := recurrence_implies_partial_sum_error_budget (N := n)
    (BONE : ℝ) T U (by norm_num [BONE]) hfirstError herrorRec
      (by omega) (by omega)
  have hsum : |exactPartial - computedFractional| < accumulatedError n := by
    rw [hexactPartial, hcomputedFractional, accumulatedError]
    convert hsumRaw using 1
    simp [U, Nat.add_comm]
  have hfeeExponent := single_sided_withdrawal_fractional_le_fee_exponent
    hweight0 hintegerPart hcomputedExponentSplit hcomputedExponentUpper
  have hfeeDominance :
      FIVE_PERCENT_MIN_FEE_RATE * |T 1| ≤
        singleSidedWithdrawalMinimumFeePowerValue weight nominalRatio / 20 := by
    exact single_sided_fee_value_dominates_reciprocal_fractional_term
      (S := (BONE : ℝ)) (fractional := a) (weight := weight)
      (q := 1 - computedBase) (nominalRatio := nominalRatio)
      (firstTerm := |T 1|)
      (feeValue := singleSidedWithdrawalMinimumFeePowerValue weight nominalRatio)
      (by norm_num [BONE]) ha0 hfeeExponent hnominal0 hdisplacement
      hfirstMagnitude rfl
  have hfractional :
      (BONE : ℝ) * computedBase ^ a - computedFractional <
        singleSidedWithdrawalMinimumFeePowerValue weight nominalRatio / 20 := by
    by_cases hnSecond : n = 2
    · have hfirstLarge : (CPOW_PRECISION : ℝ) < |T 1| := by
        have hrounded :
            (CPOW_PRECISION : ℝ) < |(firstRounded : ℝ)| := by
          rw [hfirstRounded]
          exact hcontinued 1 (by norm_num) (by omega)
        exact negative_floor_above_integer_threshold
          hfirstFloor hfirstNonpos (threshold := (CPOW_PRECISION : ℤ))
            (by exact_mod_cast hrounded)
      exact baseline_retained_second_iteration_adverse_error_lt_five_percent_min_fee
        hfirstLarge hpartialUpper (by simpa [hnSecond] using hsum) hfeeDominance
    · have hn3 : 3 ≤ n := by omega
      exact baseline_operating_band_later_adverse_error_lt_five_percent_min_fee
        T ha0 ha1 hx hrec hn3 hn46 hprevious htermError rfl
          hpartialUpper hsum hfeeDominance
  have hpowerLower : (1 / 2 : ℝ) ≤ computedBase ^ a := by
    have hexponentDirection : computedBase ^ (1 : ℝ) ≤ computedBase ^ a :=
      Real.rpow_le_rpow_of_exponent_ge hbase0 hbaseUpper ha1
    exact le_trans hbaseLower (by simpa using hexponentDirection)
  have hpartialLower : (BONE : ℝ) / 2 ≤ exactPartial := by
    have hscaled := mul_le_mul_of_nonneg_left hpowerLower
      (show (0 : ℝ) ≤ BONE by norm_num [BONE])
    calc
      (BONE : ℝ) / 2 = (BONE : ℝ) * (1 / 2 : ℝ) := by ring
      _ ≤ (BONE : ℝ) * computedBase ^ a := hscaled
      _ ≤ exactPartial := hpartialUpper
  have haccumulatedMax : accumulatedError n ≤ 3151 :=
    single_sided_withdrawal_accumulated_error_le_3151 hn46
  have hcomputedFractional0 : 0 ≤ computedFractional := by
    have hpartialDifference :
        exactPartial - computedFractional < accumulatedError n :=
      lt_of_le_of_lt (le_abs_self _) hsum
    have hmargin : (3151 : ℝ) < (BONE : ℝ) / 2 := by norm_num [BONE]
    linarith
  have hwholeUpper := hwholeTrace.upper_bound hbase0.le
  have hwhole0 : 0 ≤ computedBase ^ integerPart := pow_nonneg hbase0.le _
  have hwhole1 : computedBase ^ integerPart ≤ 1 :=
    pow_le_one₀ hbase0.le hbaseUpper
  have hcomposedUpper : wholeComputed * computedFractional ≤ computedPower := by
    rw [hcomputedPower]
    exact hcomposedCeil.le
  have hfeePositive :
      0 < singleSidedWithdrawalMinimumFeePowerValue weight nominalRatio := by
    rw [singleSidedWithdrawalMinimumFeePowerValue, minimum_fee_rate_value]
    have hfeeExponentPositive : 0 < (1 - weight) / weight :=
      div_pos (by linarith) hweight0
    exact mul_pos (by norm_num)
      (mul_pos (mul_pos (by norm_num [BONE]) hfeeExponentPositive)
        hnominalPositive)
  have hcomposed := below_one_upper_composition_preserves_adverse_bound
    hwhole0 hwhole1 hcomputedFractional0 hwholeUpper hcomposedUpper
      (div_pos hfeePositive (by norm_num)) hfractional
  have hexact :
      (BONE : ℝ) * computedBase ^ computedExponent =
        computedBase ^ integerPart * ((BONE : ℝ) * computedBase ^ a) := by
    rw [hcomputedExponentSplit, Real.rpow_add hbase0]
    norm_num [Real.rpow_natCast]
    ring
  rw [hexact]
  exact hcomposed

/-- Positive weight complement and burn ratio make the minimum-fee scale positive. -/
theorem single_sided_withdrawal_minimum_fee_power_value_positive
    {weight nominalRatio : ℝ}
    (hweight0 : 0 < weight) (hweight1 : weight < 1)
    (hnominal : 0 < nominalRatio) :
    0 < singleSidedWithdrawalMinimumFeePowerValue weight nominalRatio := by
  rw [singleSidedWithdrawalMinimumFeePowerValue, minimum_fee_rate_value]
  exact mul_pos (by norm_num)
    (mul_pos
      (mul_pos (by norm_num [BONE]) (div_pos (by linarith) hweight0))
      hnominal)

/--
Below the convergence band, a successful maximum-output check makes the
withdrawal strictly pool-favoring independently of the `c_pow` result.
-/
theorem successful_single_sided_withdrawal_low_base_has_no_adverse_error
    {outputBalance scale weight feeRate nominalRatio computedBase : ℝ}
    {output maxOutput : ℤ}
    (houtputBalance : 0 < outputBalance) (hscale : 0 < scale)
    (hweight0 : 0 < weight) (hweight1 : weight < 1)
    (hfee0 : 0 ≤ feeRate)
    (hfeeUpper : feeRate ≤ (MAX_FEE : ℝ) / STROOP)
    (hratio0 : 0 ≤ nominalRatio) (hratio1 : nominalRatio < 1)
    (hbase : singleSidedWithdrawalIdealBase nominalRatio ≤ computedBase)
    (hbaseLow : computedBase < 1 / 2)
    (hmaxOutputFloor :
      IsFloor maxOutput
        (outputBalance / scale * ((MAX_OUT_RATIO : ℝ) / STROOP)))
    (hmaxOutputGuard : output ≤ maxOutput) :
    (output : ℝ) -
        singleSidedWithdrawalIdealOutput
          (outputBalance / scale) weight feeRate nominalRatio < 0 := by
  have hidealBase0 : 0 < singleSidedWithdrawalIdealBase nominalRatio := by
    rw [singleSidedWithdrawalIdealBase]
    linarith
  have hidealBase1 : singleSidedWithdrawalIdealBase nominalRatio ≤ 1 := by
    rw [singleSidedWithdrawalIdealBase]
    linarith
  have hexponentOne : 1 < 1 / weight := (one_lt_div hweight0).2 hweight1
  have hpowerHalf :
      singleSidedWithdrawalIdealBase nominalRatio ^ (1 / weight) < 1 / 2 := by
    calc
      singleSidedWithdrawalIdealBase nominalRatio ^ (1 / weight) ≤
          singleSidedWithdrawalIdealBase nominalRatio ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hidealBase0 hidealBase1 hexponentOne.le
      _ = singleSidedWithdrawalIdealBase nominalRatio := by
        rw [Real.rpow_one]
      _ ≤ computedBase := hbase
      _ < 1 / 2 := hbaseLow
  have hfeeTenth : feeRate ≤ 1 / 10 := by
    exact le_trans hfeeUpper (by norm_num [MAX_FEE, STROOP])
  have hweightedFeeUpper : singleSidedWithdrawalFeeRate weight feeRate ≤ 1 / 10 := by
    rw [singleSidedWithdrawalFeeRate]
    calc
      (1 - weight) * feeRate ≤ 1 * feeRate :=
        mul_le_mul_of_nonneg_right (by linarith) hfee0
      _ = feeRate := by ring
      _ ≤ 1 / 10 := hfeeTenth
  have hfeeMultiplierLower :
      9 / 10 ≤ 1 - singleSidedWithdrawalFeeRate weight feeRate := by
    linarith
  have hnative0 : 0 < outputBalance / scale := div_pos houtputBalance hscale
  have hgrowth :
      1 / 2 < 1 - singleSidedWithdrawalIdealBase nominalRatio ^ (1 / weight) := by
    linarith
  have hnativeGrowth :
      outputBalance / scale * (1 / 2) <
        outputBalance / scale *
          (1 - singleSidedWithdrawalIdealBase nominalRatio ^ (1 / weight)) :=
    mul_lt_mul_of_pos_left hgrowth hnative0
  have hscaledGrowth :
      outputBalance / scale * (1 / 2) * (9 / 10) <
        outputBalance / scale *
            (1 - singleSidedWithdrawalIdealBase nominalRatio ^ (1 / weight)) *
          (9 / 10) :=
    mul_lt_mul_of_pos_right hnativeGrowth (by norm_num)
  have hgrowth0 :
      0 ≤ outputBalance / scale *
        (1 - singleSidedWithdrawalIdealBase nominalRatio ^ (1 / weight)) :=
    mul_nonneg hnative0.le (le_trans (by norm_num) hgrowth.le)
  have hidealLower :
      outputBalance / scale * (9 / 20) <
        singleSidedWithdrawalIdealOutput
          (outputBalance / scale) weight feeRate nominalRatio := by
    rw [singleSidedWithdrawalIdealOutput]
    calc
      outputBalance / scale * (9 / 20) =
          outputBalance / scale * (1 / 2) * (9 / 10) := by ring
      _ < outputBalance / scale *
            (1 - singleSidedWithdrawalIdealBase nominalRatio ^ (1 / weight)) *
          (9 / 10) := hscaledGrowth
      _ ≤ outputBalance / scale *
            (1 - singleSidedWithdrawalIdealBase nominalRatio ^ (1 / weight)) *
          (1 - singleSidedWithdrawalFeeRate weight feeRate) :=
        mul_le_mul_of_nonneg_left hfeeMultiplierLower hgrowth0
  have hguardReal : (output : ℝ) ≤ (maxOutput : ℝ) := by
    exact_mod_cast hmaxOutputGuard
  have houtputCap :
      (output : ℝ) ≤
        outputBalance / scale * ((MAX_OUT_RATIO : ℝ) / STROOP) :=
    le_trans hguardReal hmaxOutputFloor.le
  have hratioBound : (MAX_OUT_RATIO : ℝ) / STROOP < 9 / 20 := by
    norm_num [MAX_OUT_RATIO, STROOP]
  have houtputUpper :
      (output : ℝ) < outputBalance / scale * (9 / 20) :=
    lt_of_le_of_lt houtputCap (mul_lt_mul_of_pos_left hratioBound hnative0)
  linarith

/-!
The following four entry theorems mirror every `c_pow` control-flow case used
by the exact-LP-input single-sided withdrawal: a later fractional stop, a
corrected first fractional stop, the unit-base shortcut, and an integer-only
exponent. The successful caller guard handles a later fractional result below
the convergence band independently of its approximation.
-/

/--
Full multi-term exact-LP-input withdrawal comparison for the modeled
production fixed-point path.
-/
theorem baseline_single_sided_withdrawal_multiterm_adverse_error_lt_five_percent_min_fee
    (coefficientProduct multiplied computedTerm : ℕ → ℤ)
    {n integerPart : ℕ}
    {poolSupply poolAmountIn nominalRatio outputBalance weight feeRate
      computedBase computedExponent a computedFractional wholeComputed
      computedPower feeMultiplier scale : ℝ}
    {computedBaseRaw computedExponentRaw firstRounded computedPowerRaw
      newBalance tokenAmountBeforeFee result output maxOutput : ℤ}
    (hpoolSupply : 0 < poolSupply) (hpoolAmountIn : 0 < poolAmountIn)
    (hnominal : nominalRatio = poolAmountIn / poolSupply)
    (hratio1 : nominalRatio < 1)
    (houtputBalance : 0 < outputBalance)
    (hweight0 : 0 < weight) (hweight1 : weight < 1)
    (hfee0 : 0 ≤ feeRate)
    (hfeeUpper : feeRate ≤ (MAX_FEE : ℝ) / STROOP)
    (hcomputedBase : computedBase = (computedBaseRaw : ℝ) / BONE)
    (hbaseCeil :
      IsCeil computedBaseRaw ((BONE : ℝ) * (1 - nominalRatio)))
    (hbaseNonunit : computedBase < 1)
    (hcomputedExponentRaw0 : 0 ≤ computedExponentRaw)
    (hcomputedExponent :
      computedExponent = (computedExponentRaw : ℝ) / BONE)
    (hexponentFloor :
      IsFloor computedExponentRaw ((BONE : ℝ) * (1 / weight)))
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hintegerPart : 1 ≤ integerPart)
    (hcomputedExponentSplit : computedExponent = (integerPart : ℝ) + a)
    (hn2 : 2 ≤ n)
    (hcontinued : ∀ k, 1 ≤ k → k < n →
      (CPOW_PRECISION : ℝ) < |(computedTerm k : ℝ)|)
    (hfirstFloor :
      IsFloor firstRounded (exactInputBinomialTerm a computedBase 1))
    (hfirstRounded : firstRounded = computedTerm 1)
    (hcoefficientFloor : ∀ k, 1 ≤ k → k < 50 →
      IsFloor (coefficientProduct (k + 1))
        ((BONE : ℝ) * (a - (k : ℝ)) * (computedBase - 1)))
    (hmultiplyTermFloor : ∀ k, 1 ≤ k → k < 50 →
      IsFloor (multiplied (k + 1))
        ((computedTerm k : ℝ) * (coefficientProduct (k + 1) : ℝ) /
          (BONE : ℝ)))
    (hdivideTermFloor : ∀ k, 1 ≤ k → k < 50 →
      IsFloor (computedTerm (k + 1))
        ((multiplied (k + 1) : ℝ) / ((k : ℝ) + 1)))
    (hcomputedFractional :
      computedFractional = (BONE : ℝ) +
        ∑ k ∈ Finset.range n, (computedTerm (k + 1) : ℝ))
    (hwholeTrace : UpperCPowiTrace computedBase integerPart wholeComputed)
    (hcomputedPower : computedPower = (computedPowerRaw : ℝ))
    (hcomposedCeil :
      IsCeil computedPowerRaw (wholeComputed * computedFractional))
    (hfeeMultiplier :
      feeMultiplier = 1 - singleSidedWithdrawalFeeRate weight feeRate)
    (hscale : 0 < scale)
    (hnewBalanceCeil :
      IsCeil newBalance (outputBalance * (computedPower / (BONE : ℝ))))
    (htokenAmount :
      (tokenAmountBeforeFee : ℝ) = outputBalance - (newBalance : ℝ))
    (hfeeFloor :
      IsFloor result ((tokenAmountBeforeFee : ℝ) * feeMultiplier))
    (hdownscaleFloor : IsFloor output ((result : ℝ) / scale))
    (hmaxOutputFloor :
      IsFloor maxOutput
        (outputBalance / scale * ((MAX_OUT_RATIO : ℝ) / STROOP)))
    (hmaxOutputGuard : output ≤ maxOutput) :
    (output : ℝ) -
        singleSidedWithdrawalIdealOutput
          (outputBalance / scale) weight feeRate nominalRatio <
      singleSidedWithdrawalMinimumFeeOutputValue
        (outputBalance / scale) weight nominalRatio / 20 := by
  have hnominal0 : 0 ≤ nominalRatio := by rw [hnominal]; positivity
  have hnominalPositive : 0 < nominalRatio := by rw [hnominal]; positivity
  have hbase := single_sided_withdrawal_base_ceil_refines
    hnominal0 hcomputedBase hbaseCeil
  have hexponent := single_sided_withdrawal_exponent_floor_refines
    hcomputedExponentRaw0 hcomputedExponent hexponentFloor
  have hdisplacement := single_sided_withdrawal_displacement_le_nominal_ratio
    hbase.1
  have hfee1 : feeRate ≤ 1 :=
    le_trans hfeeUpper (by norm_num [MAX_FEE, STROOP])
  by_cases hbaseLower : 1 / 2 ≤ computedBase
  · have hcpow :=
      baseline_single_sided_withdrawal_cpow_multiterm_adverse_error_lt_five_percent_min_fee
        coefficientProduct multiplied computedTerm hweight0 hweight1 hnominal0
          hnominalPositive ha0 ha1 hintegerPart hcomputedExponentSplit
          hexponent.2 hbaseLower hbase.2 hbaseNonunit hdisplacement hn2
          hcontinued hfirstFloor hfirstRounded hcoefficientFloor
          hmultiplyTermFloor hdivideTermFloor hcomputedFractional hwholeTrace
          hcomputedPower hcomposedCeil
    exact single_sided_withdrawal_from_fixed_point_refinements
      hpoolSupply hpoolAmountIn hnominal hratio1 houtputBalance hweight0
        hweight1 hfee0 hfee1 hcomputedBase hbaseCeil hcomputedExponentRaw0
        hcomputedExponent hexponentFloor hcpow hfeeMultiplier hscale
        hnewBalanceCeil htokenAmount hfeeFloor hdownscaleFloor
  · have hpoolFavoring :=
      successful_single_sided_withdrawal_low_base_has_no_adverse_error
        houtputBalance hscale hweight0 hweight1 hfee0 hfeeUpper hnominal0
          hratio1 hbase.1 (lt_of_not_ge hbaseLower) hmaxOutputFloor
          hmaxOutputGuard
    have hminimumOutputPositive :
        0 < singleSidedWithdrawalMinimumFeeOutputValue
          (outputBalance / scale) weight nominalRatio / 20 := by
      rw [singleSidedWithdrawalMinimumFeeOutputValue, minimum_fee_rate_value]
      have hfeeExponentPositive : 0 < (1 - weight) / weight :=
        div_pos (by linarith) hweight0
      positivity
    linarith

/--
Full corrected-first-term exact-LP-input withdrawal comparison. The `c_pow`
contribution has zero adverse error before the caller's pool-favoring rounds.
-/
theorem baseline_single_sided_withdrawal_first_term_adverse_error_lt_five_percent_min_fee
    {integerPart : ℕ}
    {poolSupply poolAmountIn nominalRatio outputBalance weight feeRate
      computedBase computedExponent a wholeComputed computedPower feeMultiplier
      scale : ℝ}
    {computedBaseRaw computedExponentRaw firstRounded computedPowerRaw
      newBalance tokenAmountBeforeFee result output : ℤ}
    (hpoolSupply : 0 < poolSupply) (hpoolAmountIn : 0 < poolAmountIn)
    (hnominal : nominalRatio = poolAmountIn / poolSupply)
    (hratio1 : nominalRatio < 1)
    (houtputBalance : 0 < outputBalance)
    (hweight0 : 0 < weight) (hweight1 : weight < 1)
    (hfee0 : 0 ≤ feeRate) (hfee1 : feeRate ≤ 1)
    (hcomputedBase : computedBase = (computedBaseRaw : ℝ) / BONE)
    (hbaseCeil :
      IsCeil computedBaseRaw ((BONE : ℝ) * (1 - nominalRatio)))
    (hcomputedExponentRaw0 : 0 ≤ computedExponentRaw)
    (hcomputedExponent :
      computedExponent = (computedExponentRaw : ℝ) / BONE)
    (hexponentFloor :
      IsFloor computedExponentRaw ((BONE : ℝ) * (1 / weight)))
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hcomputedExponentSplit : computedExponent = (integerPart : ℝ) + a)
    (hfirstFloor :
      IsFloor firstRounded ((BONE : ℝ) * a * (computedBase - 1)))
    (hwholeTrace : UpperCPowiTrace computedBase integerPart wholeComputed)
    (hcomputedPower : computedPower = (computedPowerRaw : ℝ))
    (hcomposedCeil :
      IsCeil computedPowerRaw
        (wholeComputed * ((BONE : ℝ) + (firstRounded : ℝ) + 1)))
    (hfeeMultiplier :
      feeMultiplier = 1 - singleSidedWithdrawalFeeRate weight feeRate)
    (hscale : 0 < scale)
    (hnewBalanceCeil :
      IsCeil newBalance (outputBalance * (computedPower / (BONE : ℝ))))
    (htokenAmount :
      (tokenAmountBeforeFee : ℝ) = outputBalance - (newBalance : ℝ))
    (hfeeFloor :
      IsFloor result ((tokenAmountBeforeFee : ℝ) * feeMultiplier))
    (hdownscaleFloor : IsFloor output ((result : ℝ) / scale)) :
    (output : ℝ) -
        singleSidedWithdrawalIdealOutput
          (outputBalance / scale) weight feeRate nominalRatio <
      singleSidedWithdrawalMinimumFeeOutputValue
        (outputBalance / scale) weight nominalRatio / 20 := by
  have hnominal0 : 0 ≤ nominalRatio := by rw [hnominal]; positivity
  have hnominalPositive : 0 < nominalRatio := by rw [hnominal]; positivity
  have hbase := single_sided_withdrawal_base_ceil_refines
    hnominal0 hcomputedBase hbaseCeil
  have hbase0 : 0 < computedBase := by
    have hideal0 : 0 < singleSidedWithdrawalIdealBase nominalRatio := by
      rw [singleSidedWithdrawalIdealBase]
      linarith
    exact lt_of_lt_of_le hideal0 hbase.1
  have hfeePositive :=
    single_sided_withdrawal_minimum_fee_power_value_positive
      hweight0 hweight1 hnominalPositive
  have hwholeUpper := hwholeTrace.upper_bound hbase0.le
  have hcomposedUpper := exact_input_final_cpow_ceil_refines
    hcomputedPower hcomposedCeil
  have hcpow :=
    baseline_exact_input_cpow_first_term_adverse_error_lt_five_percent_min_fee
      ha0 ha1 hcomputedExponentSplit hbase0 hfirstFloor hwholeUpper
        hcomposedUpper hfeePositive
  exact single_sided_withdrawal_from_fixed_point_refinements
    hpoolSupply hpoolAmountIn hnominal hratio1 houtputBalance hweight0
      hweight1 hfee0 hfee1 hcomputedBase hbaseCeil hcomputedExponentRaw0
      hcomputedExponent hexponentFloor hcpow hfeeMultiplier hscale
      hnewBalanceCeil htokenAmount hfeeFloor hdownscaleFloor

/--
Full unit-base exact-LP-input withdrawal comparison. `1 ^ exponent` is exact,
including the baseline branch that intentionally skips the first-term
correction when the displacement is zero.
-/
theorem baseline_single_sided_withdrawal_unit_base_adverse_error_lt_five_percent_min_fee
    {poolSupply poolAmountIn nominalRatio outputBalance weight feeRate
      computedBase computedExponent computedPower feeMultiplier scale : ℝ}
    {computedBaseRaw computedExponentRaw newBalance tokenAmountBeforeFee result
      output : ℤ}
    (hpoolSupply : 0 < poolSupply) (hpoolAmountIn : 0 < poolAmountIn)
    (hnominal : nominalRatio = poolAmountIn / poolSupply)
    (hratio1 : nominalRatio < 1)
    (houtputBalance : 0 < outputBalance)
    (hweight0 : 0 < weight) (hweight1 : weight < 1)
    (hfee0 : 0 ≤ feeRate) (hfee1 : feeRate ≤ 1)
    (hcomputedBase : computedBase = (computedBaseRaw : ℝ) / BONE)
    (hbaseCeil :
      IsCeil computedBaseRaw ((BONE : ℝ) * (1 - nominalRatio)))
    (hcomputedExponentRaw0 : 0 ≤ computedExponentRaw)
    (hcomputedExponent :
      computedExponent = (computedExponentRaw : ℝ) / BONE)
    (hexponentFloor :
      IsFloor computedExponentRaw ((BONE : ℝ) * (1 / weight)))
    (hunitBase : computedBase = 1)
    (hcomputedPower : computedPower = (BONE : ℝ))
    (hfeeMultiplier :
      feeMultiplier = 1 - singleSidedWithdrawalFeeRate weight feeRate)
    (hscale : 0 < scale)
    (hnewBalanceCeil :
      IsCeil newBalance (outputBalance * (computedPower / (BONE : ℝ))))
    (htokenAmount :
      (tokenAmountBeforeFee : ℝ) = outputBalance - (newBalance : ℝ))
    (hfeeFloor :
      IsFloor result ((tokenAmountBeforeFee : ℝ) * feeMultiplier))
    (hdownscaleFloor : IsFloor output ((result : ℝ) / scale)) :
    (output : ℝ) -
        singleSidedWithdrawalIdealOutput
          (outputBalance / scale) weight feeRate nominalRatio <
      singleSidedWithdrawalMinimumFeeOutputValue
        (outputBalance / scale) weight nominalRatio / 20 := by
  have hnominalPositive : 0 < nominalRatio := by rw [hnominal]; positivity
  have hfeePositive :=
    single_sided_withdrawal_minimum_fee_power_value_positive
      hweight0 hweight1 hnominalPositive
  have hconservative := baseline_exact_input_cpow_unit_base_has_no_adverse_error
    (computedExponent := computedExponent) hunitBase (le_of_eq hcomputedPower.symm)
  have hfeeShare :
      0 < singleSidedWithdrawalMinimumFeePowerValue weight nominalRatio / 20 :=
    div_pos hfeePositive (by norm_num)
  have hcpow :
      (BONE : ℝ) * computedBase ^ computedExponent - computedPower <
        singleSidedWithdrawalMinimumFeePowerValue weight nominalRatio / 20 := by
    linarith
  exact single_sided_withdrawal_from_fixed_point_refinements
    hpoolSupply hpoolAmountIn hnominal hratio1 houtputBalance hweight0
      hweight1 hfee0 hfee1 hcomputedBase hbaseCeil hcomputedExponentRaw0
      hcomputedExponent hexponentFloor hcpow hfeeMultiplier hscale
      hnewBalanceCeil htokenAmount hfeeFloor hdownscaleFloor

/--
Full integer-only exact-LP-input withdrawal comparison. The upper-rounded
`c_powi` result has zero adverse error.
-/
theorem baseline_single_sided_withdrawal_integer_adverse_error_lt_five_percent_min_fee
    {integerPart : ℕ}
    {poolSupply poolAmountIn nominalRatio outputBalance weight feeRate
      computedBase computedPower feeMultiplier scale : ℝ}
    {computedBaseRaw computedExponentRaw newBalance tokenAmountBeforeFee result
      output : ℤ}
    (hpoolSupply : 0 < poolSupply) (hpoolAmountIn : 0 < poolAmountIn)
    (hnominal : nominalRatio = poolAmountIn / poolSupply)
    (hratio1 : nominalRatio < 1)
    (houtputBalance : 0 < outputBalance)
    (hweight0 : 0 < weight) (hweight1 : weight < 1)
    (hfee0 : 0 ≤ feeRate) (hfee1 : feeRate ≤ 1)
    (hcomputedBase : computedBase = (computedBaseRaw : ℝ) / BONE)
    (hbaseCeil :
      IsCeil computedBaseRaw ((BONE : ℝ) * (1 - nominalRatio)))
    (hcomputedExponentRaw0 : 0 ≤ computedExponentRaw)
    (hcomputedExponent :
      (integerPart : ℝ) = (computedExponentRaw : ℝ) / BONE)
    (hexponentFloor :
      IsFloor computedExponentRaw ((BONE : ℝ) * (1 / weight)))
    (hwholeTrace :
      UpperCPowiTrace computedBase integerPart
        (computedPower / (BONE : ℝ)))
    (hfeeMultiplier :
      feeMultiplier = 1 - singleSidedWithdrawalFeeRate weight feeRate)
    (hscale : 0 < scale)
    (hnewBalanceCeil :
      IsCeil newBalance (outputBalance * (computedPower / (BONE : ℝ))))
    (htokenAmount :
      (tokenAmountBeforeFee : ℝ) = outputBalance - (newBalance : ℝ))
    (hfeeFloor :
      IsFloor result ((tokenAmountBeforeFee : ℝ) * feeMultiplier))
    (hdownscaleFloor : IsFloor output ((result : ℝ) / scale)) :
    (output : ℝ) -
        singleSidedWithdrawalIdealOutput
          (outputBalance / scale) weight feeRate nominalRatio <
      singleSidedWithdrawalMinimumFeeOutputValue
        (outputBalance / scale) weight nominalRatio / 20 := by
  have hnominal0 : 0 ≤ nominalRatio := by rw [hnominal]; positivity
  have hnominalPositive : 0 < nominalRatio := by rw [hnominal]; positivity
  have hbase := single_sided_withdrawal_base_ceil_refines
    hnominal0 hcomputedBase hbaseCeil
  have hbase0 : 0 < computedBase := by
    have hideal0 : 0 < singleSidedWithdrawalIdealBase nominalRatio := by
      rw [singleSidedWithdrawalIdealBase]
      linarith
    exact lt_of_lt_of_le hideal0 hbase.1
  have hwholeNormalized := hwholeTrace.upper_bound hbase0.le
  have hB : (0 : ℝ) < BONE := by norm_num [BONE]
  have hwholeUpper :
      (BONE : ℝ) * computedBase ^ integerPart ≤ computedPower := by
    have h := (le_div_iff₀ hB).mp hwholeNormalized
    simpa [mul_comm] using h
  have hconservative := baseline_exact_input_cpow_integer_has_no_adverse_error
    hwholeUpper
  have hfeePositive :=
    single_sided_withdrawal_minimum_fee_power_value_positive
      hweight0 hweight1 hnominalPositive
  have hfeeShare :
      0 < singleSidedWithdrawalMinimumFeePowerValue weight nominalRatio / 20 :=
    div_pos hfeePositive (by norm_num)
  have hcpow :
      (BONE : ℝ) * computedBase ^ (integerPart : ℝ) - computedPower <
        singleSidedWithdrawalMinimumFeePowerValue weight nominalRatio / 20 := by
    linarith
  exact single_sided_withdrawal_from_fixed_point_refinements
    hpoolSupply hpoolAmountIn hnominal hratio1 houtputBalance hweight0
      hweight1 hfee0 hfee1 hcomputedBase hbaseCeil hcomputedExponentRaw0
      hcomputedExponent hexponentFloor hcpow hfeeMultiplier hscale
      hnewBalanceCeil htokenAmount hfeeFloor hdownscaleFloor

end CometCPow
