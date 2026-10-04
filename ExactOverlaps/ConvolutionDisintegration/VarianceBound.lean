/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.ConvolutionDisintegration.WindowVariance
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# The normalized local-variance bound for W

Use the genuine sliding-window disintegration and the chord bound for
exp(-u) on the unit interval. The exact weighted variance identity supplies
the source constant 1-exp(-1), without selecting an optimal disintegration.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set

namespace ExactOverlaps.ConvolutionDisintegration

lemma exp_neg_le_chord {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    Real.exp (-u) ≤ 1 - (1 - Real.exp (-1)) * u := by
  have h : Real.exp ((1 - u) * 0 + u * (-1)) ≤
      (1 - u) * Real.exp 0 + u * Real.exp (-1) :=
    convexOn_exp.2 (mem_univ _) (mem_univ _) (sub_nonneg.mpr hu1) hu (by ring)
  simp only [mul_zero, zero_add, mul_neg_one, Real.exp_zero, mul_one] at h
  nlinarith

lemma cost_windowFamily (μ : ProbabilityMeasure ℝ) (r a : ℝ) :
    cost r (windowFamily μ r a) = Real.exp (-windowNormalizedVariance μ r a) := by
  unfold cost windowFamily
  rw [totalVariance_singleLaw]
  congr 1
  unfold windowNormalizedVariance
  ring

lemma integrable_cost_windowFamily (μ : ProbabilityMeasure ℝ) {r : ℝ} (hr : 0 < r) :
    Integrable (fun a ↦ cost r (windowFamily μ r a)) (windowMixingLaw μ hr : Measure ℝ) := by
  apply memLp_one_iff_integrable.mp
  exact MemLp.of_bound ((measurable_cost r).comp
    (measurable_windowFamily μ r)).aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun a ↦ by
      rw [Real.norm_eq_abs, abs_of_pos (cost_pos r _)]
      exact cost_le_one r _))

theorem W_le_one_sub_normalizedLocalVariance (μ : ProbabilityMeasure ℝ) {r : ℝ}
    (hr : 0 < r) : W μ r ≤
      1 - (1 - Real.exp (-1)) * (VarianceEnergy.normalizedLocalVariance (μ : Measure ℝ) r).toReal := by
  have hi := integrable_windowNormalizedVariance μ hr
  calc
    W μ r ≤ ∫ a, cost r (windowFamily μ r a) ∂(windowMixingLaw μ hr : Measure ℝ) :=
      W_le_familyCost _ _ _ (isFamilyDisintegration_window μ hr)
    _ ≤ ∫ a, (1 - (1 - Real.exp (-1)) * windowNormalizedVariance μ r a)
        ∂(windowMixingLaw μ hr : Measure ℝ) := by
      apply integral_mono (integrable_cost_windowFamily μ hr)
        ((integrable_const (1 : ℝ)).sub (hi.const_mul (1 - Real.exp (-1))))
      intro a
      change cost r (windowFamily μ r a) ≤ 1 - (1 - Real.exp (-1)) * windowNormalizedVariance μ r a
      rw [cost_windowFamily]
      exact exp_neg_le_chord (windowNormalizedVariance_nonneg μ r a)
        (windowNormalizedVariance_le_one μ hr a)
    _ = _ := by
      rw [integral_sub (integrable_const (1 : ℝ)) (hi.const_mul (1 - Real.exp (-1))),
        integral_const_mul, integral_windowNormalizedVariance μ hr]
      simp

end ExactOverlaps.ConvolutionDisintegration
