module

public import ExactOverlaps.SelfSimilar.ContractionScale

/-! Elementary growth bounds for finite displacement supports at dyadic scales. -/

@[expose] public section

namespace ExactOverlaps.SelfSimilar

theorem pow_toNat_eq_zpow {i : ℤ} (hi : 0 ≤ i) :
    (2 : ℝ) ^ i.toNat = (2 : ℝ) ^ i := by
  rw [← zpow_natCast, Int.toNat_of_nonneg hi]

theorem log_dyadic_mesh_bound (M : ℕ) {i : ℤ} (hi : 0 ≤ i) :
    Real.log (2 * ((M * 2 ^ i.toNat : ℕ) : ℝ) + 3) ≤
      Real.log (2 * M + 3 : ℝ) + (i : ℝ) * Real.log 2 := by
  have hp : 1 ≤ (2 : ℝ) ^ i := one_le_zpow₀ (by norm_num) hi
  have hpos : (0 : ℝ) < 2 * M + 3 := by positivity
  have hbound : 2 * ((M * 2 ^ i.toNat : ℕ) : ℝ) + 3 ≤
      (2 * M + 3 : ℝ) * (2 : ℝ) ^ i := by
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_toNat_eq_zpow hi]
    nlinarith
  calc
    Real.log (2 * ((M * 2 ^ i.toNat : ℕ) : ℝ) + 3) ≤
        Real.log ((2 * M + 3 : ℝ) * (2 : ℝ) ^ i) :=
      Real.log_le_log (by positivity) hbound
    _ = Real.log (2 * M + 3 : ℝ) + (i : ℝ) * Real.log 2 := by
      rw [Real.log_mul hpos.ne' (zpow_pos (by norm_num : (0 : ℝ) < 2) i).ne', Real.log_zpow]

theorem contractionScale_exp_mul_log_two_le (a : ℝ) (n : ℕ) :
    (contractionScale (Real.exp a) n : ℝ) * Real.log 2 ≤ -(n : ℝ) * a := by
  have hf := (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp
    (Int.floor_le (-(n : ℝ) * Real.log (Real.exp a) / Real.log 2))
  simpa only [contractionScale, Real.log_exp] using hf

end ExactOverlaps.SelfSimilar
