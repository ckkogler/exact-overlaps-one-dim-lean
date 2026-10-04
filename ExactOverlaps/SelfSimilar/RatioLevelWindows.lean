module

public import ExactOverlaps.SelfSimilar.RatioLevels

/-!
Common integer buffers around the typical ratio levels. These are deterministic
rounding bounds, uniform over every ratio class in the typical window.
-/

@[expose] public section

open Filter
open scoped Topology

namespace ExactOverlaps.SelfSimilar

noncomputable def bufferedRatioLevel (κ ε : ℝ) (n : ℕ) : ℤ := ⌊(κ - 2 * ε) * n⌋
noncomputable def targetRatioLevel (κ q : ℝ) (n : ℕ) : ℤ := ⌊q * κ * n⌋

theorem bufferedRatioLevel_nonneg {κ ε : ℝ} (h : 2 * ε ≤ κ) (n : ℕ) :
    0 ≤ bufferedRatioLevel κ ε n := by
  exact Int.floor_nonneg.mpr (mul_nonneg (sub_nonneg.mpr h) (Nat.cast_nonneg n))

theorem typical_level_lower_buffer {κ ε : ℝ} {n : ℕ} {j : ℤ}
    (hj : (κ - ε) * n ≤ (j : ℝ)) :
    ε * n ≤ ((j - bufferedRatioLevel κ ε n : ℤ) : ℝ) := by
  have hf := Int.floor_le ((κ - 2 * ε) * n)
  simp only [Int.cast_sub, bufferedRatioLevel]
  nlinarith

theorem typical_level_upper_buffer {κ ε q : ℝ} {n : ℕ} {j : ℤ}
    (hj : (j : ℝ) ≤ (κ + ε) * n) :
    ((q - 1) * κ - ε) * n - 1 < ((targetRatioLevel κ q n - j : ℤ) : ℝ) := by
  have hf := Int.lt_floor_add_one (q * κ * n)
  simp only [Int.cast_sub, targetRatioLevel]
  nlinarith

/-- Every fixed integer margin eventually fits on both sides of all typical classes. -/
theorem eventually_typical_level_buffers {κ ε q : ℝ} (hε : 0 < ε)
    (hgap : 0 < (q - 1) * κ - ε) (D : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℤ,
      (κ - ε) * n ≤ (j : ℝ) → (j : ℝ) ≤ (κ + ε) * n →
      (D : ℤ) ≤ j - bufferedRatioLevel κ ε n ∧
        (D : ℤ) ≤ targetRatioLevel κ q n - j := by
  have hevent₁ : ∀ᶠ n : ℕ in atTop, (D : ℝ) / ε ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  have hevent₂ : ∀ᶠ n : ℕ in atTop,
      ((D : ℝ) + 1) / ((q - 1) * κ - ε) ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hevent₁, hevent₂] with n hn₁ hn₂
  intro j hj₁ hj₂
  have hb₁ := typical_level_lower_buffer hj₁
  have hb₂ := typical_level_upper_buffer (q := q) hj₂
  have h₁ := (div_le_iff₀ hε).mp hn₁
  have h₂ := (div_le_iff₀ hgap).mp hn₂
  constructor
  · exact_mod_cast (show (D : ℝ) ≤ ((j - bufferedRatioLevel κ ε n : ℤ) : ℝ) by nlinarith)
  · exact_mod_cast (show (D : ℝ) ≤ ((targetRatioLevel κ q n - j : ℤ) : ℝ) by nlinarith)

/-- Floor rounding disappears after division by the word length. -/
theorem floor_linear_div_tendsto (c : ℝ) :
    Tendsto (fun n : ℕ ↦ (⌊c * n⌋ : ℤ) / (n : ℝ)) atTop (𝓝 c) := by
  have hl : Tendsto (fun n : ℕ ↦ c - 1 / (n : ℝ)) atTop (𝓝 c) := by
    simpa only [sub_zero] using
      tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    apply (le_div_iff₀ hn').mpr
    have hf := Int.lt_floor_add_one (c * n)
    have he : (c - 1 / (n : ℝ)) * n = c * n - 1 := by field_simp
    rw [he]
    linarith
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    exact (div_le_iff₀ hn').mpr (Int.floor_le (c * n))

theorem bufferedRatioLevel_div_tendsto (κ ε : ℝ) :
    Tendsto (fun n : ℕ ↦ (bufferedRatioLevel κ ε n : ℝ) / n) atTop (𝓝 (κ - 2 * ε)) :=
  floor_linear_div_tendsto (κ - 2 * ε)

theorem targetRatioLevel_div_tendsto (κ q : ℝ) :
    Tendsto (fun n : ℕ ↦ (targetRatioLevel κ q n : ℝ) / n) atTop (𝓝 (q * κ)) :=
  floor_linear_div_tendsto (q * κ)

end ExactOverlaps.SelfSimilar
