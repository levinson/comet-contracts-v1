import Mathlib

namespace CometCPow

/-- The two inequalities required from a mathematically exact floor operation. -/
structure IsFloor (rounded : ℤ) (exact : ℝ) : Prop where
  le : (rounded : ℝ) ≤ exact
  lt_add_one : exact < rounded + 1

/-- The two inequalities required from a mathematically exact ceiling operation. -/
structure IsCeil (rounded : ℤ) (exact : ℝ) : Prop where
  le : exact ≤ (rounded : ℝ)
  add_one_lt : rounded - 1 < exact

theorem IsFloor.abs_error_lt_one {rounded : ℤ} {exact : ℝ}
    (h : IsFloor rounded exact) : |exact - rounded| < 1 := by
  rw [abs_of_nonneg (sub_nonneg.mpr h.le)]
  linarith [h.lt_add_one]

theorem IsCeil.abs_error_lt_one {rounded : ℤ} {exact : ℝ}
    (h : IsCeil rounded exact) : |(rounded : ℝ) - exact| < 1 := by
  rw [abs_of_nonneg (sub_nonneg.mpr h.le)]
  linarith [h.add_one_lt]

theorem floor_isFloor (x : ℝ) : IsFloor ⌊x⌋ x := by
  constructor
  · exact Int.floor_le x
  · exact Int.lt_floor_add_one x

theorem ceil_isCeil (x : ℝ) : IsCeil ⌈x⌉ x := by
  constructor
  · exact Int.le_ceil x
  · linarith [Int.ceil_lt_add_one x]

/-- Dividing an exact ceiling by a positive scale adds less than one scaled unit. -/
theorem normalized_ceil_lt_exact_add_inv_scale
    {rounded : ℤ} {exact scale : ℝ}
    (hscale : 0 < scale) (hceil : IsCeil rounded (scale * exact)) :
    (rounded : ℝ) / scale < exact + 1 / scale := by
  apply (div_lt_iff₀ hscale).2
  have hraw : (rounded : ℝ) < scale * exact + 1 := by
    linarith [hceil.add_one_lt]
  calc
    (rounded : ℝ) < scale * exact + 1 := hraw
    _ = (exact + 1 / scale) * scale := by
      field_simp
      ring

/-- Normalizing a raw mathematical floor preserves its lower-bound direction. -/
theorem IsFloor.normalized_le
    {rounded : ℤ} {exact scale : ℝ}
    (h : IsFloor rounded (scale * exact)) (hscale : 0 < scale) :
    (rounded : ℝ) / scale ≤ exact := by
  apply (div_le_iff₀ hscale).2
  simpa [mul_comm] using h.le

/-- Normalizing a raw mathematical ceiling preserves its upper-bound direction. -/
theorem IsCeil.le_normalized
    {rounded : ℤ} {exact scale : ℝ}
    (h : IsCeil rounded (scale * exact)) (hscale : 0 < scale) :
    exact ≤ (rounded : ℝ) / scale := by
  apply (le_div_iff₀ hscale).2
  simpa [mul_comm] using h.le

/-- A ceiling of a value below an integer upper bound cannot exceed that bound. -/
theorem IsCeil.le_integer_upper
    {rounded upper : ℤ} {exact : ℝ}
    (h : IsCeil rounded exact) (hexactUpper : exact ≤ (upper : ℝ)) :
    rounded ≤ upper := by
  by_contra hnot
  have hlower : upper + 1 ≤ rounded := by omega
  have hlowerReal : (upper : ℝ) + 1 ≤ (rounded : ℝ) := by exact_mod_cast hlower
  linarith [h.add_one_lt]

end CometCPow
