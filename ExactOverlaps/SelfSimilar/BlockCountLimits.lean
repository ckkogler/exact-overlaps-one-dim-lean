module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic

/-! Exact asymptotics of the number of full blocks and the final short block. -/

@[expose] public section

open Filter
open scoped Topology

namespace ExactOverlaps.SelfSimilar

theorem nat_remainder_div_tendsto_zero {N : ℕ} (hN : 0 < N) :
    Tendsto (fun n : ℕ ↦ (n % N : ℕ) / (n : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero (fun n ↦ div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg n))
    (fun n ↦ div_le_div_of_nonneg_right (by exact_mod_cast (Nat.mod_lt n hN).le)
      (Nat.cast_nonneg n)) (tendsto_const_div_atTop_nhds_zero_nat (N : ℝ))

theorem nat_quotient_div_tendsto {N : ℕ} (hN : 0 < N) :
    Tendsto (fun n : ℕ ↦ (n / N : ℕ) / (n : ℝ)) atTop (𝓝 (1 / (N : ℝ))) := by
  have hc : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have h := (hc.sub (nat_remainder_div_tendsto_zero hN)).div_const (N : ℝ)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have he : (n % N : ℕ) + (N : ℝ) * (n / N : ℕ) = n := by
    exact_mod_cast Nat.mod_add_div n N
  field_simp [hn', hN']
  nlinarith

theorem block_count_div_tendsto {N : ℕ} (hN : 0 < N) :
    Tendsto (fun n : ℕ ↦ ((n / N : ℕ) + 1 : ℝ) / n) atTop (𝓝 (1 / (N : ℝ))) := by
  have h := (nat_quotient_div_tendsto hN).add (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  simpa only [add_zero, add_div] using h

end ExactOverlaps.SelfSimilar
