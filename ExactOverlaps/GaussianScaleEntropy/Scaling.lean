/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.GaussianScaleEntropy.Envelope
public import ExactOverlaps.GaussianApproximation.ScalarTransport

/-!
# Normalization of the actual law and physical entropy scale

Dividing a sampled value by r sends its scale-r quantizer exactly to the
unit quantizer with the corresponding physical translation. Change of
variables then gives exact averaged entropy scaling, while actual moments
and the genuine Wasserstein distance scale by their usual powers.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set

namespace ExactOverlaps.GaussianScaleEntropy

def normalize (μ : ProbabilityMeasure ℝ) (r : ℝ) : ProbabilityMeasure ℝ :=
  μ.map (fun x ↦ r⁻¹ * x)

lemma law_normalize (μ : ProbabilityMeasure ℝ) {r : ℝ} (hr : r ≠ 0) (t : ℝ) :
    ScaleEntropy.law (normalize μ r) 1 t = ScaleEntropy.law μ r (r * t) := by
  have hm : Measurable (fun x : ℝ ↦ r⁻¹ * x) := by fun_prop
  apply PMF.toMeasure_injective
  rw [ScaleEntropy.law_toMeasure, ScaleEntropy.law_toMeasure, normalize,
    ProbabilityMeasure.toMeasure_map,
    Measure.map_map (ScaleEntropy.measurable_quantize 1 t) hm]
  congr 1
  funext x
  change ScaleEntropy.quantize 1 t (r⁻¹ * x) = ScaleEntropy.quantize r (r * t) x
  unfold ScaleEntropy.quantize
  apply congrArg Int.floor
  field_simp

lemma cellEntropy_normalize (μ : ProbabilityMeasure ℝ) {r : ℝ} (hr : r ≠ 0) (t : ℝ) :
    cellEntropy (normalize μ r) 1 t = cellEntropy μ r (r * t) := by
  simp only [cellEntropy, cellTerm, law_normalize μ hr]

lemma shiftedEntropy_normalize (μ : ProbabilityMeasure ℝ) {r : ℝ} (hr : r ≠ 0) (t : ℝ) :
    shiftedEntropy (normalize μ r) 1 t = shiftedEntropy μ r (r * t) := by
  rw [shiftedEntropy, shiftedEntropy, cellEntropy_normalize μ hr]

lemma entropy_normalize (μ : ProbabilityMeasure ℝ) {r : ℝ} (hr : r ≠ 0) :
    entropy (normalize μ r) 1 = entropy μ r := by
  simp only [entropy, div_one, shiftedEntropy_normalize μ hr]
  rw [intervalIntegral.integral_comp_mul_left _ hr]
  simp only [mul_zero, mul_one, smul_eq_mul, div_eq_mul_inv, mul_comm]

lemma integrable_id_normalize (μ : ProbabilityMeasure ℝ)
    (hμ : Integrable (fun x : ℝ ↦ x) (μ : Measure ℝ)) (r : ℝ) :
    Integrable (fun x : ℝ ↦ x) (normalize μ r : Measure ℝ) :=
  GaussianApproximation.integrable_id_map_mul μ hμ r⁻¹

lemma integrable_sq_normalize (μ : ProbabilityMeasure ℝ)
    (hμ : Integrable (fun x : ℝ ↦ x ^ 2) (μ : Measure ℝ)) (r : ℝ) :
    Integrable (fun x : ℝ ↦ x ^ 2) (normalize μ r : Measure ℝ) := by
  have hm : Measurable (fun x : ℝ ↦ r⁻¹ * x) := by fun_prop
  have hs : Measurable (fun x : ℝ ↦ x ^ 2) := by fun_prop
  rw [normalize, ProbabilityMeasure.toMeasure_map]
  apply (integrable_map_measure hs.aestronglyMeasurable hm.aemeasurable).mpr
  change Integrable (fun x : ℝ ↦ (r⁻¹ * x) ^ 2) (μ : Measure ℝ)
  simpa only [mul_pow] using hμ.const_mul (r⁻¹ ^ 2)

lemma secondMoment_normalize (μ : ProbabilityMeasure ℝ) (r : ℝ) :
    (∫ x, x ^ 2 ∂(normalize μ r : Measure ℝ)) =
      r⁻¹ ^ 2 * ∫ x, x ^ 2 ∂(μ : Measure ℝ) := by
  have hm : Measurable (fun x : ℝ ↦ r⁻¹ * x) := by fun_prop
  have hs : Measurable (fun x : ℝ ↦ x ^ 2) := by fun_prop
  rw [normalize, ProbabilityMeasure.toMeasure_map,
    integral_map hm.aemeasurable hs.aestronglyMeasurable]
  simp only [mul_pow, integral_const_mul]

lemma secondMoment_normalize_le (μ : ProbabilityMeasure ℝ) {r B : ℝ} (hr : r ≠ 0)
    (hμ : (∫ x, x ^ 2 ∂(μ : Measure ℝ)) ≤ B * r ^ 2) :
    (∫ x, x ^ 2 ∂(normalize μ r : Measure ℝ)) ≤ B := by
  rw [secondMoment_normalize]
  have h := mul_le_mul_of_nonneg_left hμ (sq_nonneg r⁻¹)
  have he : r⁻¹ ^ 2 * (B * r ^ 2) = B := by field_simp
  exact h.trans_eq he

lemma wasserstein_normalize_le (μ ν : ProbabilityMeasure ℝ)
    (hμ : Integrable (fun x : ℝ ↦ x) (μ : Measure ℝ))
    (hν : Integrable (fun x : ℝ ↦ x) (ν : Measure ℝ)) {r : ℝ} (hr : 0 < r) :
    GaussianApproximation.wasserstein1 (normalize μ r) (normalize ν r)
      (integrable_id_normalize μ hμ r) (integrable_id_normalize ν hν r) ≤
      r⁻¹ * GaussianApproximation.wasserstein1 μ ν hμ hν :=
  GaussianApproximation.wasserstein1_map_mul_le μ ν hμ hν (inv_pos.mpr hr)

end ExactOverlaps.GaussianScaleEntropy
