/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.GaussianEntropyGrowth.GaussianInformation

/-!
# Averaging the Gaussian information estimate

A uniform shifted-entropy estimate survives averaging over the physical
translation parameter. This yields an explicit mesh-size error for the
entropy of a Gaussian probability law.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace ExactOverlaps.GaussianEntropyGrowth

open GaussianApproximation GaussianScaleEntropy

lemma entropy_error_of_shifted (μ : ProbabilityMeasure ℝ)
    (hμ : Integrable (fun x : ℝ ↦ x ^ 2) (μ : Measure ℝ))
    {r c K : ℝ} (hr : 0 < r)
    (h : ∀ t ∈ Icc 0 r, |shiftedEntropy μ r t - c| ≤ K) :
    |entropy μ r - c| ≤ K := by
  have hi := intervalIntegrable_shiftedEntropy_at_scale μ hμ hr
  have hb : |∫ t in (0 : ℝ)..r, shiftedEntropy μ r t - c| ≤ K * r := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := r) (f := fun t ↦ shiftedEntropy μ r t - c) (C := K)
      (fun t ht ↦ by
        rw [uIoc_of_le hr.le] at ht
        simpa only [Real.norm_eq_abs] using h t ⟨ht.1.le, ht.2⟩)
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_pos hr] using hb
  rw [intervalIntegral.integral_sub hi intervalIntegrable_const,
    intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hb
  have he : entropy μ r - c =
      ((∫ t in (0 : ℝ)..r, shiftedEntropy μ r t) - r * c) / r := by
    unfold entropy
    field_simp
  rw [he, abs_div, abs_of_pos hr]
  exact (div_le_iff₀ hr).mpr hb

lemma entropy_gaussian_error (v : ℝ≥0) (hv : 0 < (v : ℝ))
    {r : ℝ} (hr : 0 < r) :
    |entropy (centeredGaussian v) r -
      (gaussianDifferentialEntropy v - Real.log r)| ≤
      ((∫ x, |x| ∂(centeredGaussian v : Measure ℝ)) + r) * r / (v : ℝ) :=
  entropy_error_of_shifted (centeredGaussian v) (integrable_sq_centeredGaussian v) hr
    (fun _ ht ↦ shiftedEntropy_gaussian_error v hv hr ht)

lemma entropy_gaussian_error_sigma {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r) :
    |entropy (centeredGaussian (NNReal.mk (σ ^ 2) (sq_nonneg σ))) r -
      (gaussianDifferentialEntropy (NNReal.mk (σ ^ 2) (sq_nonneg σ)) - Real.log r)| ≤
      (σ * gaussianFirstMoment + r) * r / σ ^ 2 := by
  have hv : 0 < (NNReal.mk (σ ^ 2) (sq_nonneg σ) : ℝ) := sq_pos_of_pos hσ
  simpa only [gaussian_firstMoment_scale hσ, NNReal.coe_mk] using
    entropy_gaussian_error (NNReal.mk (σ ^ 2) (sq_nonneg σ)) hv hr

end ExactOverlaps.GaussianEntropyGrowth
