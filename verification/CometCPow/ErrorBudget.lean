import Mathlib

namespace CometCPow

/-- The three new floors in recurrence step `k` add less than three raw units of error. -/
theorem recurrence_increment_lt_three {S D k : ℝ}
    (hS : 0 < S) (hD : D < S) (hk : 2 ≤ k) :
    (1 + 1 / (k * S)) * D + 1 / k + 1 / k + 1 < D + 3 := by
  have hk0 : 0 < k := lt_of_lt_of_le (by norm_num) hk
  have hkS0 : 0 < k * S := mul_pos hk0 hS
  have hDkS : D < k * S := by
    have hSkS : S ≤ k * S := by nlinarith
    exact lt_of_lt_of_le hD hSkS
  have hfracD : D / (k * S) < 1 := (div_lt_one hkS0).2 hDkS
  have hfracK : 1 / k + 1 / k ≤ 1 := by
    calc
      1 / k + 1 / k = 2 / k := by ring
      _ ≤ 1 := (div_le_one hk0).2 hk
  calc
    (1 + 1 / (k * S)) * D + 1 / k + 1 / k + 1 =
        D + D / (k * S) + (1 / k + 1 / k) + 1 := by ring
    _ < D + 1 + 1 + 1 := by linarith
    _ = D + 3 := by ring

/-- Induction principle used by the implementation's `3k - 2` term-error budget. -/
theorem linear_error_budget (D : ℕ → ℝ)
    (hbase : D 1 < 1)
    (hstep : ∀ n, 1 ≤ n → n < 50 → D (n + 1) < D n + 3) :
    ∀ n, 1 ≤ n → n ≤ 50 → D n < 3 * (n : ℝ) - 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn h50
      cases n with
      | zero => omega
      | succ m =>
          by_cases hm : m = 0
          · subst m
            norm_num
            exact hbase
          · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
            have hm50 : m ≤ 50 := le_trans (Nat.le_succ m) h50
            have hmlt : m < 50 := Nat.lt_of_succ_le h50
            have hi := ih m (Nat.lt_succ_self m) hm1 hm50
            have hs := hstep m hm1 hmlt
            push_cast at hi hs ⊢
            nlinarith

/-- The raw recurrence inequality implies the implementation's `3k - 2` budget. -/
theorem recurrence_error_budget (S : ℝ) (D : ℕ → ℝ)
    (hS : 148 < S)
    (hbase : D 1 < 1)
    (hrec : ∀ n, 1 ≤ n → n < 50 →
      D (n + 1) <
        (1 + 1 / (((n + 1 : ℕ) : ℝ) * S)) * D n +
          1 / ((n + 1 : ℕ) : ℝ) + 1 / ((n + 1 : ℕ) : ℝ) + 1) :
    ∀ n, 1 ≤ n → n ≤ 50 → D n < 3 * (n : ℝ) - 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn h50
      cases n with
      | zero => omega
      | succ m =>
          by_cases hm : m = 0
          · subst m
            norm_num
            exact hbase
          · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
            have hm50 : m ≤ 50 := le_trans (Nat.le_succ m) h50
            have hmlt : m < 50 := Nat.lt_of_succ_le h50
            have hi := ih m (Nat.lt_succ_self m) hm1 hm50
            have hmReal : (m : ℝ) < 50 := by exact_mod_cast hmlt
            have hDmS : D m < S := by nlinarith
            have hk : (2 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
              exact_mod_cast Nat.succ_le_succ hm1
            have hraw := hrec m hm1 hmlt
            have hincrement := recurrence_increment_lt_three
              (S := S) (D := D m) (k := ((m + 1 : ℕ) : ℝ)) (by nlinarith) hDmS hk
            have hstep : D (m + 1) < D m + 3 := lt_trans hraw hincrement
            push_cast at hi hstep ⊢
            nlinarith

/-- Closed form for the sum of the per-term budgets `3k - 2`, for `k = 1..N`. -/
theorem sum_error_budget (N : ℕ) :
    (∑ k ∈ Finset.range N, (3 * ((k + 1 : ℕ) : ℝ) - 2)) =
      (3 * (N : ℝ) ^ 2 - N) / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      simp only [Finset.mem_range, true_and, ih]
      push_cast
      ring

/--
Pointwise `3k - 2` term-error bounds imply the corresponding strict bound on
the accumulated finite sum. This is the bridge from the recurrence induction
to the partial sum consumed by the adverse-error theorem.
-/
theorem partial_sum_error_lt_sum_error_budget
    (exactTerm computedTerm : ℕ → ℝ) {N : ℕ}
    (hN : 1 ≤ N)
    (hterm : ∀ k, 1 ≤ k → k ≤ N →
      |exactTerm k - computedTerm k| < 3 * (k : ℝ) - 2) :
    |(∑ k ∈ Finset.range N, exactTerm (k + 1)) -
        (∑ k ∈ Finset.range N, computedTerm (k + 1))| <
      (3 * (N : ℝ) ^ 2 - N) / 2 := by
  have hrange : (Finset.range N).Nonempty := by
    refine ⟨0, Finset.mem_range.mpr ?_⟩
    omega
  have hpointwise : ∀ k ∈ Finset.range N,
      |exactTerm (k + 1) - computedTerm (k + 1)| <
        3 * (((k + 1 : ℕ) : ℝ)) - 2 := by
    intro k hk
    apply hterm (k + 1)
    · omega
    · exact Nat.succ_le_iff.mpr (Finset.mem_range.mp hk)
  calc
    |(∑ k ∈ Finset.range N, exactTerm (k + 1)) -
          (∑ k ∈ Finset.range N, computedTerm (k + 1))| =
        |∑ k ∈ Finset.range N,
          (exactTerm (k + 1) - computedTerm (k + 1))| := by
            rw [Finset.sum_sub_distrib]
    _ ≤ ∑ k ∈ Finset.range N,
          |exactTerm (k + 1) - computedTerm (k + 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ < ∑ k ∈ Finset.range N,
          (3 * (((k + 1 : ℕ) : ℝ)) - 2) :=
      Finset.sum_lt_sum_of_nonempty hrange hpointwise
    _ = (3 * (N : ℝ) ^ 2 - N) / 2 := sum_error_budget N

/--
The raw recurrence inequality discharges both the pointwise term budget and
the accumulated finite-sum budget used by the baseline `c_pow` proof.
-/
theorem recurrence_implies_partial_sum_error_budget
    (S : ℝ) (exactTerm computedTerm : ℕ → ℝ) {N : ℕ}
    (hS : 148 < S)
    (hbase : |exactTerm 1 - computedTerm 1| < 1)
    (hrec : ∀ n, 1 ≤ n → n < 50 →
      |exactTerm (n + 1) - computedTerm (n + 1)| <
        (1 + 1 / (((n + 1 : ℕ) : ℝ) * S)) *
            |exactTerm n - computedTerm n| +
          1 / ((n + 1 : ℕ) : ℝ) + 1 / ((n + 1 : ℕ) : ℝ) + 1)
    (hN1 : 1 ≤ N) (hN50 : N ≤ 50) :
    |(∑ k ∈ Finset.range N, exactTerm (k + 1)) -
        (∑ k ∈ Finset.range N, computedTerm (k + 1))| <
      (3 * (N : ℝ) ^ 2 - N) / 2 := by
  have hterm := recurrence_error_budget S
    (fun k ↦ |exactTerm k - computedTerm k|) hS hbase hrec
  exact partial_sum_error_lt_sum_error_budget exactTerm computedTerm hN1
    (fun k hk1 hkN ↦ hterm k hk1 (le_trans hkN hN50))

/-- In the common `0 ≤ q ≤ 1/2` case, the geometric-tail factor is in `[0, 1]`. -/
theorem geometric_factor_bounds {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) :
    0 ≤ q / (1 - q) ∧ q / (1 - q) ≤ 1 := by
  have hdenom : 0 < 1 - q := by linarith
  constructor
  · positivity
  · exact (div_le_one hdenom).2 (by linarith)

theorem geometric_tail_le_current {term q : ℝ}
    (hterm : 0 ≤ term) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) :
    term * (q / (1 - q)) ≤ term := by
  exact mul_le_of_le_one_right hterm (geometric_factor_bounds hq0 hq).2

end CometCPow
