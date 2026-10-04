module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.SpecificLimits.Basic

/-! Dyadic rounding of the geometric contraction scale, using natural logarithms. -/

@[expose] public section

namespace ExactOverlaps.SelfSimilar

/-- Integer dyadic level corresponding to n contractions of absolute ratio c. -/
noncomputable def contractionScale (c : ℝ) (n : ℕ) : ℤ :=
  ⌊-(n : ℝ) * Real.log c / Real.log 2⌋

theorem contractionScale_mul_pow_le_one {c : ℝ} (hc : 0 < c) (n : ℕ) :
    (2 : ℝ) ^ contractionScale c n * c ^ n ≤ 1 := by
  have htwo : (0 : ℝ) < 2 := by norm_num
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hf := (le_div_iff₀ hlog).mp
    (Int.floor_le (-(n : ℝ) * Real.log c / Real.log 2))
  apply (Real.log_le_log_iff
    (mul_pos (zpow_pos htwo _) (pow_pos hc _)) zero_lt_one).mp
  rw [Real.log_mul (zpow_pos htwo _).ne' (pow_pos hc _).ne',
    Real.log_zpow, Real.log_pow, Real.log_one]
  dsimp [contractionScale]
  linarith

theorem contractionScale_nonneg {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (n : ℕ) :
    0 ≤ contractionScale c n := by
  apply Int.floor_nonneg.mpr
  apply div_nonneg _ (Real.log_nonneg (by norm_num))
  exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (Nat.cast_nonneg n))
    (Real.log_nonpos hc.le hc1)

end ExactOverlaps.SelfSimilar
