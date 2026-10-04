/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.GaussianApproximation.GaussianScaling
public import ExactOverlaps.Entropy.GaussianCDF
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Actual Gaussian second moments and uniform CDF regularity

The comparison laws are Mathlib's centered Gaussians. Their genuine
second moment is the variance parameter, and a positive lower standard
deviation supplies a single CDF Lipschitz constant for the entire family.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ExactOverlaps.GaussianScaleEntropy

open GaussianApproximation

lemma integrable_sq_centeredGaussian (v : ℝ≥0) :
    Integrable (fun x : ℝ ↦ x ^ 2) (centeredGaussian v : Measure ℝ) := by
  have h2 : MemLp (id : ℝ → ℝ) (2 : ℕ) (gaussianReal 0 v) := memLp_id_gaussianReal 2
  simpa only [centeredGaussian, ProbabilityMeasure.coe_mk, Real.norm_eq_abs, sq_abs, id_eq]
    using h2.integrable_norm_pow'

lemma secondMoment_centeredGaussian (v : ℝ≥0) :
    (∫ x, x ^ 2 ∂(centeredGaussian v : Measure ℝ)) = (v : ℝ) := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral (X := fun x : ℝ ↦ x) (by fun_prop)] at h
  simpa only [centeredGaussian, ProbabilityMeasure.coe_mk, integral_id_gaussianReal, sub_zero] using h

lemma integrable_id_of_secondMoment (μ : ProbabilityMeasure ℝ)
    (hμ : Integrable (fun x : ℝ ↦ x ^ 2) (μ : Measure ℝ)) :
    Integrable (fun x : ℝ ↦ x) (μ : Measure ℝ) := by
  have h2 := (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr hμ
  exact h2.integrable (by norm_num)

def gaussianCDFBound (a : ℝ) : ℝ≥0 :=
  ⟨(Real.sqrt (2 * Real.pi * a ^ 2))⁻¹, by positivity⟩

lemma centeredGaussian_cdf_lipschitz {a σ : ℝ} (ha : 0 < a) (hσ : a ≤ σ) :
    LipschitzWith (gaussianCDFBound a)
      (cdf (centeredGaussian ⟨σ ^ 2, sq_nonneg σ⟩ : Measure ℝ)) := by
  unfold centeredGaussian gaussianCDFBound
  exact Entropy.gaussian_cdf_lipschitz 0 (⟨σ ^ 2, sq_nonneg σ⟩ : ℝ≥0)
    (sq_pos_of_pos ha) (show a ^ 2 ≤ σ ^ 2 by nlinarith)

end ExactOverlaps.GaussianScaleEntropy
