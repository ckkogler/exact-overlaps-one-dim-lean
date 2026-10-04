module

public import ExactOverlaps.SelfSimilar.ContractionScale

/-! Rounding bounds between buffered and unbuffered logarithmic scales. -/

@[expose] public section

namespace ExactOverlaps.SelfSimilar

theorem contractionScale_exp_add_le (a : ℝ) {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) :
    contractionScale (Real.exp (a + ε)) n ≤ contractionScale (Real.exp a) n := by
  apply Int.floor_mono
  simp only [Real.log_exp]
  apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by norm_num))
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

theorem contractionScale_exp_gap_le (a ε : ℝ) (n : ℕ) :
    ((contractionScale (Real.exp a) n - contractionScale (Real.exp (a + ε)) n : ℤ) : ℝ) *
      Real.log 2 ≤ (n : ℝ) * ε + Real.log 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hj := (le_div_iff₀ hlog).mp
    (Int.floor_le (-(n : ℝ) * Real.log (Real.exp a) / Real.log 2))
  have hi := (div_lt_iff₀ hlog).mp
    (Int.lt_floor_add_one (-(n : ℝ) * Real.log (Real.exp (a + ε)) / Real.log 2))
  simp only [Real.log_exp] at hj hi
  simp only [Int.cast_sub, contractionScale, Real.log_exp]
  nlinarith

end ExactOverlaps.SelfSimilar
