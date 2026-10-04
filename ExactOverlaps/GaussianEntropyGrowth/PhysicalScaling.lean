/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.GaussianScaleEntropy.GaussianContinuity

/-!
# Scaling arbitrary physical entropy meshes

Successive normalization of an actual probability law composes exactly.
Consequently the averaged entropy at any nonzero physical scale transforms
by the same scale factor, including differences between two scales.
-/

@[expose] public section

noncomputable section
open MeasureTheory

namespace ExactOverlaps.GaussianEntropyGrowth

open GaussianScaleEntropy

lemma normalize_normalize (μ : ProbabilityMeasure ℝ) (r s : ℝ) :
    normalize (normalize μ r) s = normalize μ (r * s) := by
  have hr : Measurable (fun x : ℝ ↦ r⁻¹ * x) := by fun_prop
  have hs : Measurable (fun x : ℝ ↦ s⁻¹ * x) := by fun_prop
  apply ProbabilityMeasure.toMeasure_injective
  simp only [GaussianScaleEntropy.normalize, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map hs hr]
  congr 1
  funext x
  change s⁻¹ * (r⁻¹ * x) = (r * s)⁻¹ * x
  simp only [mul_inv_rev]
  ring

lemma entropy_normalize_scale (μ : ProbabilityMeasure ℝ) {r s : ℝ}
    (hr : r ≠ 0) (hs : s ≠ 0) :
    entropy (normalize μ r) s = entropy μ (r * s) := by
  rw [← entropy_normalize (normalize μ r) hs, normalize_normalize,
    entropy_normalize μ (mul_ne_zero hr hs)]

lemma entropyBetween_normalize (μ : ProbabilityMeasure ℝ) {r s S : ℝ}
    (hr : r ≠ 0) (hs : s ≠ 0) (hS : S ≠ 0) :
    entropyBetween (normalize μ r) s S = entropyBetween μ (r * s) (r * S) := by
  unfold entropyBetween
  rw [entropy_normalize_scale μ hr hs, entropy_normalize_scale μ hr hS]

lemma mean_normalize (μ : ProbabilityMeasure ℝ) (r : ℝ) :
    (∫ x, x ∂(normalize μ r : Measure ℝ)) = r⁻¹ * ∫ x, x ∂(μ : Measure ℝ) := by
  have hr : Measurable (fun x : ℝ ↦ r⁻¹ * x) := by fun_prop
  rw [GaussianScaleEntropy.normalize, ProbabilityMeasure.toMeasure_map,
    integral_map (f := fun x : ℝ ↦ x) hr.aemeasurable measurable_id.aestronglyMeasurable]
  exact integral_const_mul _ _

end ExactOverlaps.GaussianEntropyGrowth
