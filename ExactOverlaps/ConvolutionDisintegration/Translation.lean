/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.ConvolutionDisintegration.ConvolutionBound

/-!
# Translation invariance of W

Translation is actual convolution with a point mass. Submultiplicativity
and the unit upper bound give one inequality, and translation back gives
the reverse inequality. No minimizing disintegration is presumed to exist.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set

namespace ExactOverlaps.ConvolutionDisintegration

lemma convolution_diracLaw (μ : ProbabilityMeasure ℝ) (b : ℝ) :
    Entropy.realConvolution μ (diracLaw b) = μ.map (fun x ↦ x + b) := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [Entropy.realConvolution_toMeasure]
  exact Measure.conv_dirac (μ : Measure ℝ) b

lemma map_add_inverse (μ : ProbabilityMeasure ℝ) (b : ℝ) :
    (μ.map (fun x ↦ x + b)).map (fun x ↦ x + -b) = μ := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((μ : Measure ℝ).map (fun x ↦ x + b)).map (fun x ↦ x + -b) = _
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have he : (fun x : ℝ ↦ x + -b) ∘ (fun x ↦ x + b) = id := by
    funext x
    simp
  rw [he, Measure.map_id]

lemma W_map_add_le {r : ℝ} (hr : 0 ≤ r) (μ : ProbabilityMeasure ℝ) (b : ℝ) :
    W (μ.map (fun x ↦ x + b)) r ≤ W μ r := by
  rw [← convolution_diracLaw]
  exact (W_convolution_le hr μ (diracLaw b)).trans
    (by simpa using mul_le_mul_of_nonneg_left (W_le_one hr (diracLaw b)) (W_nonneg hr μ))

theorem W_map_add {r : ℝ} (hr : 0 ≤ r) (μ : ProbabilityMeasure ℝ) (b : ℝ) :
    W (μ.map (fun x ↦ x + b)) r = W μ r := by
  apply le_antisymm (W_map_add_le hr μ b)
  have h := W_map_add_le hr (μ.map (fun x ↦ x + b)) (-b)
  rwa [map_add_inverse] at h

end ExactOverlaps.ConvolutionDisintegration
