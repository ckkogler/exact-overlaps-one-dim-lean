/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.GaussianScaleEntropy.UnitContinuity
public import ExactOverlaps.GaussianScaleEntropy.GaussianMoments
public import ExactOverlaps.GaussianScaleEntropy.FiniteMoments

/-!
# Uniform scale-entropy continuity near centered Gaussian laws

The modulus is uniform over a compact positive standard-deviation range.
The approximating law may be unbounded and is controlled only through
its genuine second moment and genuine Wasserstein distance.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace ExactOverlaps.GaussianScaleEntropy

open GaussianApproximation

lemma normalize_centeredGaussian (σ r : ℝ) :
    normalize (centeredGaussian (NNReal.mk (σ ^ 2) (sq_nonneg σ))) r =
      centeredGaussian (NNReal.mk ((σ / r) ^ 2) (sq_nonneg (σ / r))) := by
  have hv : NNReal.mk (r⁻¹ ^ 2) (sq_nonneg r⁻¹) * (NNReal.mk (σ ^ 2) (sq_nonneg σ)) =
      (NNReal.mk ((σ / r) ^ 2) (sq_nonneg (σ / r))) := by
    apply NNReal.eq
    change r⁻¹ ^ 2 * σ ^ 2 = (σ / r) ^ 2
    simp only [div_eq_mul_inv, mul_pow, inv_pow, mul_comm]
  have h := gaussianReal_map_const_mul (μ := 0) (v := (NNReal.mk (σ ^ 2) (sq_nonneg σ))) r⁻¹
  rw [mul_zero, hv] at h
  apply ProbabilityMeasure.toMeasure_injective
  rw [normalize, ProbabilityMeasure.toMeasure_map]
  simpa only [centeredGaussian, ProbabilityMeasure.coe_mk] using h

theorem gaussian_entropy_continuity_unit {a b ε : ℝ}
    (ha : 0 < a) (hab : a < b) (hε : 0 < ε) :
    ∃ δ > 0, ∀ (σ : ℝ), σ ∈ Icc a b → ∀ (μ : ProbabilityMeasure ℝ)
      (hμ2 : Integrable (fun x : ℝ ↦ x ^ 2) (μ : Measure ℝ)),
      (∫ x, x ^ 2 ∂(μ : Measure ℝ)) ≤ b ^ 2 →
      wasserstein1 μ (centeredGaussian (NNReal.mk (σ ^ 2) (sq_nonneg σ)))
        (integrable_id_of_secondMoment μ hμ2) (integrable_id_centeredGaussian _) < δ →
      |entropy μ 1 - entropy (centeredGaussian (NNReal.mk (σ ^ 2) (sq_nonneg σ))) 1| < ε := by
  obtain ⟨δ, hδ, hu⟩ := exists_uniform_entropy_modulus (sq_nonneg b) (gaussianCDFBound a) hε
  refine ⟨δ, hδ, ?_⟩
  intro σ hσ μ hμ2 hμB hW
  have hσB : σ ^ 2 ≤ b ^ 2 := by nlinarith [hσ.1, hσ.2]
  apply hu μ _ (integrable_id_of_secondMoment μ hμ2) (integrable_id_centeredGaussian _)
    hμ2 (integrable_sq_centeredGaussian _) hμB _ (centeredGaussian_cdf_lipschitz ha hσ.1) hW
  exact (secondMoment_centeredGaussian (NNReal.mk (σ ^ 2) (sq_nonneg σ))).trans_le hσB

/-- Primary Lemma 3.8, with an actual possibly unbounded probability law. -/
theorem gaussian_entropy_continuity {a b ε : ℝ}
    (ha : 0 < a) (hab : a < b) (hε : 0 < ε) :
    ∃ δ > 0, ∀ (r σ : ℝ), 0 < r → σ ∈ Icc (a * r) (b * r) →
      ∀ (μ : ProbabilityMeasure ℝ)
        (hμ2 : Integrable (fun x : ℝ ↦ x ^ 2) (μ : Measure ℝ)),
      (∫ x, x ∂(μ : Measure ℝ)) = 0 →
      (∫ x, x ^ 2 ∂(μ : Measure ℝ)) ≤ b ^ 2 * r ^ 2 →
      wasserstein1 μ (centeredGaussian (NNReal.mk (σ ^ 2) (sq_nonneg σ)))
        (integrable_id_of_secondMoment μ hμ2) (integrable_id_centeredGaussian _) < δ * r →
      |entropy μ r - entropy (centeredGaussian (NNReal.mk (σ ^ 2) (sq_nonneg σ))) r| < ε := by
  obtain ⟨δ, hδ, hu⟩ := gaussian_entropy_continuity_unit ha hab hε
  refine ⟨δ, hδ, ?_⟩
  intro r σ hr hσ μ hμ2 _hmean hμB hW
  have hσr : σ / r ∈ Icc a b :=
    ⟨(le_div_iff₀ hr).mpr hσ.1, (div_le_iff₀ hr).mpr hσ.2⟩
  have hnorm := wasserstein_normalize_le μ (centeredGaussian (NNReal.mk (σ ^ 2) (sq_nonneg σ)))
    (integrable_id_of_secondMoment μ hμ2) (integrable_id_centeredGaussian _) hr
  have hsmall : r⁻¹ * wasserstein1 μ (centeredGaussian (NNReal.mk (σ ^ 2) (sq_nonneg σ)))
      (integrable_id_of_secondMoment μ hμ2) (integrable_id_centeredGaussian _) < δ := by
    have h := mul_lt_mul_of_pos_left hW (inv_pos.mpr hr)
    have he : r⁻¹ * (δ * r) = δ := by field_simp
    exact h.trans_eq he
  have hWnorm := hnorm.trans_lt hsmall
  have hWunit : wasserstein1 (normalize μ r)
      (centeredGaussian (NNReal.mk ((σ / r) ^ 2) (sq_nonneg (σ / r))))
      (integrable_id_of_secondMoment _ (integrable_sq_normalize μ hμ2 r))
      (integrable_id_centeredGaussian _) < δ := by
    simpa only [wasserstein1, normalize_centeredGaussian] using hWnorm
  have hresult := hu (σ / r) hσr (normalize μ r) (integrable_sq_normalize μ hμ2 r)
    (secondMoment_normalize_le μ hr.ne' hμB) hWunit
  rw [← normalize_centeredGaussian σ r, entropy_normalize μ hr.ne',
    entropy_normalize _ hr.ne'] at hresult
  exact hresult

end ExactOverlaps.GaussianScaleEntropy
