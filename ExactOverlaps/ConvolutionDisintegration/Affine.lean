/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.ConvolutionDisintegration.Scaling
public import ExactOverlaps.ConvolutionDisintegration.Translation

/-! # Full signed affine covariance of the convolution-disintegration functional -/

@[expose] public section

noncomputable section
open MeasureTheory

namespace ExactOverlaps.ConvolutionDisintegration

lemma map_affine_eq (μ : ProbabilityMeasure ℝ) (a b : ℝ) :
    μ.map (fun x ↦ a * x + b) = (scaleLaw a μ).map (fun x ↦ x + b) := by
  apply ProbabilityMeasure.toMeasure_injective
  change (μ : Measure ℝ).map (fun x ↦ a * x + b) =
    ((μ : Measure ℝ).map (fun x ↦ a * x)).map (fun x ↦ x + b)
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

theorem W_map_affine {a r : ℝ} (ha : a ≠ 0) (hr : 0 < r)
    (μ : ProbabilityMeasure ℝ) (b : ℝ) :
    W (μ.map (fun x ↦ a * x + b)) r = W μ (r / |a|) := by
  rw [map_affine_eq, W_map_add hr.le, W_scaleLaw ha hr]

end ExactOverlaps.ConvolutionDisintegration
