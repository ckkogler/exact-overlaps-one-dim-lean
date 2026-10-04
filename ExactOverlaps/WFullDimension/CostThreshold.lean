/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.ConvolutionDisintegration.FactorSpace

/-!
Exponential variance cost controls the contribution of low-variance
components. A pointwise inequality avoids any choice of exceptional-set
representative when integrating over arbitrary disintegrations.
-/

@[expose] public section

noncomputable section
namespace ExactOverlaps.WFullDimension

open ConvolutionDisintegration

theorem one_le_cost_multiple_of_variance_le {δ r A : ℝ}
    (hδ : 0 < δ) (hr : 0 < r) (c : FactorFamily)
    (hv : totalVariance c ≤ A * r ^ 2) :
    1 ≤ Real.exp (4 * A / δ ^ 2) * cost (δ * r) c := by
  rw [cost, ← Real.exp_add, Real.one_le_exp_iff]
  have he : 4 * A / δ ^ 2 + (-4 / (δ * r) ^ 2 * totalVariance c) =
      (4 / (δ ^ 2 * r ^ 2)) * (A * r ^ 2 - totalVariance c) := by
    field_simp
    ring
  rw [he]
  exact mul_nonneg (by positivity) (sub_nonneg.mpr hv)

theorem entropy_lower_bound_from_cost {δ r A L H : ℝ}
    (hδ : 0 < δ) (hr : 0 < r) (hL : 0 ≤ L) (hH : 0 ≤ H)
    (c : FactorFamily) (hlarge : A * r ^ 2 ≤ totalVariance c → L ≤ H) :
    L * (1 - Real.exp (4 * A / δ ^ 2) * cost (δ * r) c) ≤ H := by
  by_cases hv : A * r ^ 2 ≤ totalVariance c
  · apply le_trans _ (hlarge hv)
    have hc : 0 ≤ Real.exp (4 * A / δ ^ 2) * cost (δ * r) c :=
      mul_nonneg (Real.exp_nonneg _) (cost_pos _ _).le
    nlinarith
  · have hc := one_le_cost_multiple_of_variance_le hδ hr c (le_of_not_ge hv)
    exact (mul_nonpos_of_nonneg_of_nonpos hL (sub_nonpos.mpr hc)).trans hH

end ExactOverlaps.WFullDimension
