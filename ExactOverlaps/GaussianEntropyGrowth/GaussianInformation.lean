/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.GaussianEntropyGrowth.GaussianCellBounds

/-!
# Integrating Gaussian cell information

The Gaussian logarithmic density is integrable because it is a constant
plus a quadratic function. The pointwise mesh error has an integrable
first-moment bound, which gives a uniform shifted-entropy estimate.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace ExactOverlaps.GaussianEntropyGrowth

open GaussianApproximation GaussianScaleEntropy

def gaussianInformation (v : ℝ≥0) (x : ℝ) : ℝ := -Real.log (gaussianPDFReal 0 v x)

def gaussianDifferentialEntropy (v : ℝ≥0) : ℝ :=
  ∫ x, gaussianInformation v x ∂(centeredGaussian v : Measure ℝ)

lemma gaussianInformation_eq (v : ℝ≥0) (hv : 0 < (v : ℝ)) (x : ℝ) :
    gaussianInformation v x =
      -Real.log ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹) + x ^ 2 / (2 * (v : ℝ)) := by
  have hp : 0 < (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by positivity
  unfold gaussianInformation gaussianPDFReal
  rw [Real.log_mul hp.ne' (Real.exp_pos _).ne', Real.log_exp, sub_zero]
  ring

lemma integrable_gaussianInformation (v : ℝ≥0) (hv : 0 < (v : ℝ)) :
    Integrable (gaussianInformation v) (centeredGaussian v : Measure ℝ) := by
  have he : gaussianInformation v = fun x ↦
      -Real.log ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹) + x ^ 2 / (2 * (v : ℝ)) :=
    funext (gaussianInformation_eq v hv)
  rw [he]
  exact (integrable_const _).add ((integrable_sq_centeredGaussian v).div_const _)

lemma integrable_gaussianCellError (v : ℝ≥0) (r : ℝ) :
    Integrable (gaussianCellError v r) (centeredGaussian v : Measure ℝ) :=
  (((integrable_id_centeredGaussian v).abs.add (integrable_const r)).mul_const r).div_const _

lemma integral_gaussianCellError (v : ℝ≥0) (r : ℝ) :
    (∫ x, gaussianCellError v r x ∂(centeredGaussian v : Measure ℝ)) =
      ((∫ x, |x| ∂(centeredGaussian v : Measure ℝ)) + r) * r / (v : ℝ) := by
  unfold gaussianCellError
  rw [integral_div, integral_mul_const,
    integral_add (integrable_id_centeredGaussian v).abs (integrable_const r)]
  simp

lemma shiftedEntropy_gaussian_error (v : ℝ≥0) (hv : 0 < (v : ℝ))
    {r t : ℝ} (hr : 0 < r) (ht : t ∈ Icc 0 r) :
    |shiftedEntropy (centeredGaussian v) r t -
      (gaussianDifferentialEntropy v - Real.log r)| ≤
      ((∫ x, |x| ∂(centeredGaussian v : Measure ℝ)) + r) * r / (v : ℝ) := by
  have hs := summable_cellTerm_at_scale (centeredGaussian v) (integrable_sq_centeredGaussian v) hr ht
  have hi := integrable_cellInformation (centeredGaussian v) r t hs
  have hg := integrable_gaussianInformation v hv
  have hdiff : Integrable (fun x ↦
      cellInformation (centeredGaussian v) r t x - gaussianInformation v x)
      (centeredGaussian v : Measure ℝ) := hi.sub hg
  have hsum : Integrable (fun x ↦
      cellInformation (centeredGaussian v) r t x - gaussianInformation v x + Real.log r)
      (centeredGaussian v : Measure ℝ) := hdiff.add (integrable_const _)
  have hbound :
      (∫ x, |cellInformation (centeredGaussian v) r t x - gaussianInformation v x + Real.log r|
        ∂(centeredGaussian v : Measure ℝ)) ≤
      ∫ x, gaussianCellError v r x ∂(centeredGaussian v : Measure ℝ) := by
    apply integral_mono hsum.abs (integrable_gaussianCellError v r)
    intro x
    change |cellInformation (centeredGaussian v) r t x - gaussianInformation v x +
      Real.log r| ≤ gaussianCellError v r x
    simpa only [gaussianInformation, sub_neg_eq_add] using abs_gaussian_cellInformation_error v hv hr t x
  have h := abs_integral_le_integral_abs.trans hbound
  rw [integral_add hdiff (integrable_const _), integral_sub hi hg,
    ← shiftedEntropy_eq_integral_information _ r t hs, integral_gaussianCellError] at h
  have hmass : (centeredGaussian v : Measure ℝ).real univ = 1 := by simp
  simpa only [gaussianDifferentialEntropy, integral_const, hmass, one_smul,
    sub_eq_add_neg, neg_add_rev, neg_neg, add_assoc, add_comm, add_left_comm] using h

lemma gaussian_firstMoment_scale {σ : ℝ} (hσ : 0 < σ) :
    (∫ x, |x| ∂(centeredGaussian (NNReal.mk (σ ^ 2) (sq_nonneg σ)) : Measure ℝ)) =
      σ * gaussianFirstMoment := by
  have he : standardGaussian.map (fun x ↦ σ * x) =
      centeredGaussian (NNReal.mk (σ ^ 2) (sq_nonneg σ)) := standardGaussian_map_mul σ
  rw [← he, ProbabilityMeasure.toMeasure_map,
    integral_map (by fun_prop)
      (show Measurable (fun x : ℝ ↦ |x|) by fun_prop).aestronglyMeasurable]
  simp only [abs_mul, abs_of_pos hσ, integral_const_mul, gaussianFirstMoment]

end ExactOverlaps.GaussianEntropyGrowth
