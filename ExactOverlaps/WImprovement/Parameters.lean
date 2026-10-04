/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic

/-! Uniform sampling constants and the vanishing relative-scale bound. -/

@[expose] public section

open Filter
open scoped Topology

namespace ExactOverlaps.WImprovement

lemma log_inv_pos {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    0 < Real.log ρ⁻¹ := Real.log_pos (one_lt_inv₀ hρ |>.mpr hρ1)

lemma sampling_margin {η L : ℝ} (hη : 0 < η) (hL : 0 < L)
    {n : ℕ} (hn : 1 < n) :
    ((n : ℝ) + 1) * L * (η / (2 * L)) < η * n := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  have he : ((n : ℝ) + 1) * L * (η / (2 * L)) = η * ((n : ℝ) + 1) / 2 := by
    field_simp
  rw [he]
  nlinarith

lemma exp_sampling_gap {ρ : ℝ} (hρ : 0 < ρ) (n : ℕ) :
    Real.exp (((n : ℝ) + 1) * Real.log ρ⁻¹) = (ρ ^ (n + 1))⁻¹ := by
  rw [show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by norm_num,
    Real.exp_nat_mul, Real.exp_log (inv_pos.mpr hρ), inv_pow]

lemma separation_division {ρ x y : ℝ} (hρ : 0 < ρ) (n : ℕ)
    (h : Real.exp (((n : ℝ) + 1) * Real.log ρ⁻¹) * x ≤ y) :
    x / ρ ^ n ≤ ρ * y := by
  rw [exp_sampling_gap hρ, ← div_eq_inv_mul] at h
  have hh := (div_le_iff₀ (pow_pos hρ (n + 1))).mp h
  apply (div_le_iff₀ (pow_pos hρ n)).mpr
  simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hh

lemma exponential_relative_scale_eq {ρ C : ℝ} (_hρ : ρ ≠ 0) (_hC : C ≠ 0) (n : ℕ) :
    C ^ (-(n : ℤ)) / ρ ^ (n + 1) = ρ⁻¹ * ((C * ρ)⁻¹) ^ n := by
  simp only [zpow_neg, zpow_natCast, div_eq_mul_inv, mul_inv_rev, mul_pow, pow_succ, inv_pow]
  ring

theorem relative_scale_tendsto_zero {ρ C : ℝ} (hρ : 0 < ρ) (hCρ : 1 < C * ρ) :
    Tendsto (fun n : ℕ ↦ C ^ (-(n : ℤ)) / ρ ^ (n + 1)) atTop (𝓝 0) := by
  have hC : 0 < C := (mul_pos_iff_of_pos_right hρ).mp (zero_lt_one.trans hCρ)
  have hbase : 0 ≤ (C * ρ)⁻¹ := inv_nonneg.mpr (zero_lt_one.trans hCρ).le
  have hbase1 : (C * ρ)⁻¹ < 1 := (inv_lt_one₀ (zero_lt_one.trans hCρ)).mpr hCρ
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hbase hbase1).const_mul ρ⁻¹
  simpa only [← exponential_relative_scale_eq hρ.ne' hC.ne', mul_zero] using ht

end ExactOverlaps.WImprovement
