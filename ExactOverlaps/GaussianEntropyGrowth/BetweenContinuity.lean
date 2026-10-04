/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.GaussianScaleEntropy.GaussianContinuity

/-!
# Gaussian continuity for entropy between two scales

The modulus for a fixed positive scale ratio is obtained from the actual
single-scale modulus at both physical scales. The comparison law is
allowed to be unbounded and has its genuine second moment controlled.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace ExactOverlaps.GaussianEntropyGrowth

open GaussianApproximation GaussianScaleEntropy

lemma gaussian_entropyBetween_continuity {a b C ε : ℝ}
    (ha : 0 < a) (hab : a < b) (hC : 0 < C) (hε : 0 < ε) :
    ∃ δ > 0, ∀ (r σ : ℝ), 0 < r → σ ∈ Icc (a * r) (b * r) →
      ∀ (μ : ProbabilityMeasure ℝ)
        (hμ2 : Integrable (fun x : ℝ ↦ x ^ 2) (μ : Measure ℝ)),
      (∫ x, x ∂(μ : Measure ℝ)) = 0 →
      (∫ x, x ^ 2 ∂(μ : Measure ℝ)) ≤ b ^ 2 * r ^ 2 →
      wasserstein1 μ (centeredGaussian (NNReal.mk (σ ^ 2) (sq_nonneg σ)))
        (integrable_id_of_secondMoment μ hμ2) (integrable_id_centeredGaussian _) < δ * r →
      |entropyBetween μ r (C * r) -
        entropyBetween (centeredGaussian (NNReal.mk (σ ^ 2) (sq_nonneg σ))) r (C * r)| < ε := by
  obtain ⟨δ₁, hδ₁, h₁⟩ := gaussian_entropy_continuity ha hab (half_pos hε)
  obtain ⟨δ₂, hδ₂, h₂⟩ := gaussian_entropy_continuity
    (div_pos ha hC) ((div_lt_div_iff_of_pos_right hC).mpr hab) (half_pos hε)
  refine ⟨min δ₁ (δ₂ * C), lt_min hδ₁ (mul_pos hδ₂ hC), ?_⟩
  intro r σ hr hσ μ hμ2 hmean hB hW
  have hW₁ : wasserstein1 μ (centeredGaussian (NNReal.mk (σ ^ 2) (sq_nonneg σ)))
      (integrable_id_of_secondMoment μ hμ2) (integrable_id_centeredGaussian _) < δ₁ * r :=
    hW.trans_le (mul_le_mul_of_nonneg_right (min_le_left _ _) hr.le)
  have hW₂ : wasserstein1 μ (centeredGaussian (NNReal.mk (σ ^ 2) (sq_nonneg σ)))
      (integrable_id_of_secondMoment μ hμ2) (integrable_id_centeredGaussian _) < δ₂ * (C * r) := by
    have h := hW.trans_le (mul_le_mul_of_nonneg_right (min_le_right _ _) hr.le)
    simpa only [mul_assoc] using h
  have haC : a / C * (C * r) = a * r := by field_simp
  have hbC : b / C * (C * r) = b * r := by field_simp
  have hBC : (b / C) ^ 2 * (C * r) ^ 2 = b ^ 2 * r ^ 2 := by field_simp
  have hσ₂ : σ ∈ Icc ((a / C) * (C * r)) ((b / C) * (C * r)) := by
    simpa only [haC, hbC] using hσ
  have hB₂ : (∫ x, x ^ 2 ∂(μ : Measure ℝ)) ≤ (b / C) ^ 2 * (C * r) ^ 2 := by
    simpa only [hBC] using hB
  have he₁ := h₁ r σ hr hσ μ hμ2 hmean hB hW₁
  have he₂ := h₂ (C * r) σ (mul_pos hC hr) hσ₂ μ hμ2 hmean hB₂ hW₂
  let G := centeredGaussian (NNReal.mk (σ ^ 2) (sq_nonneg σ))
  have he : entropyBetween μ r (C * r) - entropyBetween G r (C * r) =
      (entropy μ r - entropy G r) - (entropy μ (C * r) - entropy G (C * r)) := by
    unfold entropyBetween
    ring
  change |entropyBetween μ r (C * r) - entropyBetween G r (C * r)| < ε
  rw [he]
  exact (abs_sub _ _).trans_lt (by linarith [add_lt_add he₁ he₂])

end ExactOverlaps.GaussianEntropyGrowth
