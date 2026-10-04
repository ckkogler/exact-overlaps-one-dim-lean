module

public import ExactOverlaps.SelfSimilar.RatioLevelWindows

/-! Explicit errors for the remaining fine depth after a typical contraction. -/

@[expose] public section

namespace ExactOverlaps.SelfSimilar

theorem typical_remainder_ratio_bounds {κ η q : ℝ} {n : ℕ} (hn : 0 < n)
    {j : ℤ} (hjlo : (κ - η) * n ≤ (j : ℝ))
    (hjhi : (j : ℝ) ≤ (κ + η) * n) :
    |((targetRatioLevel κ q n - j : ℤ) : ℝ) / n - (q - 1) * κ| ≤ η + 1 / n ∧
      ((targetRatioLevel κ q n - j : ℤ) : ℝ) / n ≤ (q - 1) * κ + η := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hflo := Int.lt_floor_add_one (q * κ * n)
  have hfhi := Int.floor_le (q * κ * n)
  have hlow : (q - 1) * κ - η - 1 / n ≤
      ((targetRatioLevel κ q n - j : ℤ) : ℝ) / n := by
    apply (le_div_iff₀ hn').mpr
    have he : ((q - 1) * κ - η - 1 / (n : ℝ)) * n =
        ((q - 1) * κ - η) * n - 1 := by field_simp
    rw [he]
    simp only [targetRatioLevel, Int.cast_sub]
    nlinarith
  have hupp : ((targetRatioLevel κ q n - j : ℤ) : ℝ) / n ≤ (q - 1) * κ + η := by
    apply (div_le_iff₀ hn').mpr
    simp only [targetRatioLevel, Int.cast_sub]
    nlinarith
  refine ⟨?_, hupp⟩
  rw [abs_le]
  have hninv : (0 : ℝ) ≤ 1 / n := div_nonneg zero_le_one hn'.le
  constructor <;> linarith

theorem normalized_tail_error_bound {H d m n c δ η A L : ℝ}
    (hn : 0 < n) (hd : 0 ≤ d) (hδ : 0 ≤ δ) (hL : 0 ≤ L)
    (herror : |H - d * (m * L)| ≤ δ * (m * L))
    (hnear : |m / n - c| ≤ 2 * η) (hupper : m / n ≤ A) :
    |H / n - d * c * L| ≤ δ * A * L + 2 * d * η * L := by
  have he : H / n - d * (m / n) * L = (H - d * (m * L)) / n := by ring
  have hfirst : |H / n - d * (m / n) * L| ≤ δ * A * L := by
    rw [he, abs_div, abs_of_pos hn]
    calc
      _ ≤ (δ * (m * L)) / n := div_le_div_of_nonneg_right herror hn.le
      _ = δ * (m / n) * L := by ring
      _ ≤ δ * A * L := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hupper hδ) hL
  have hsecond : |d * (m / n) * L - d * c * L| ≤ 2 * d * η * L := by
    have he₂ : d * (m / n) * L - d * c * L = (d * L) * (m / n - c) := by ring
    rw [he₂, abs_mul, abs_of_nonneg (mul_nonneg hd hL)]
    calc
      _ ≤ d * L * (2 * η) := mul_le_mul_of_nonneg_left hnear (mul_nonneg hd hL)
      _ = _ := by ring
  exact (abs_sub_le _ (d * (m / n) * L) _).trans (add_le_add hfirst hsecond)

end ExactOverlaps.SelfSimilar
