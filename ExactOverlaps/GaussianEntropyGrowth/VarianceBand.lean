/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.GaussianEntropyGrowth.GaussianLargeVariance
public import ExactOverlaps.GaussianEntropyGrowth.BetweenContinuity
public import ExactOverlaps.GaussianEntropyGrowth.PhysicalScaling
public import ExactOverlaps.GaussianApproximation.BoundedSumApproximation

/-!
# Entropy growth in a controlled variance band

A centered law with variance in a fixed high band and sufficiently small
genuine Wasserstein error has entropy between the two prescribed scales
arbitrarily close to the maximal value. All thresholds are uniform over
the physical scale and the probability law.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace ExactOverlaps.GaussianEntropyGrowth

open GaussianApproximation GaussianScaleEntropy

lemma entropy_growth_variance_band {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε) :
    ∃ δ > 0, ∃ A > 0, δ ≤ 1 ∧ ∀ (r : ℝ), 0 < r →
      ∀ (μ : ProbabilityMeasure ℝ)
        (hμ2 : Integrable (fun x : ℝ ↦ x ^ 2) (μ : Measure ℝ)) (v : ℝ≥0),
      (∫ x, x ∂(μ : Measure ℝ)) = 0 →
      (∫ x, x ^ 2 ∂(μ : Measure ℝ)) = (v : ℝ) →
      A * r ^ 2 ≤ (v : ℝ) → (v : ℝ) ≤ (A + 1) * r ^ 2 →
      wasserstein1 μ (centeredGaussian v)
        (integrable_id_of_secondMoment μ hμ2) (integrable_id_centeredGaussian v) ≤
          gaussianApproximationConstant * (δ * r) →
      Real.log C - ε < entropyBetween μ r (C * r) := by
  obtain ⟨S, hS, hlarge⟩ := gaussian_large_variance C hC (half_pos hε)
  obtain ⟨η, hη, hcont⟩ := gaussian_entropyBetween_continuity hS
    (show S < S + 1 by linarith) hC (half_pos hε)
  let K := gaussianApproximationConstant
  have hK : 0 < K := gaussianApproximationConstant_pos
  let δ := min 1 (η / (2 * K))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hη (by positivity))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hKδ : K * δ < η := by
    have h := (le_div_iff₀ (show 0 < 2 * K by positivity)).mp (min_le_right 1 (η / (2 * K)))
    change δ * (2 * K) ≤ η at h
    nlinarith
  refine ⟨δ, hδ, S ^ 2, sq_pos_of_pos hS, hδ1, ?_⟩
  intro r hr μ hμ2 v hmean hmoment hlo hhi hW
  let σ := Real.sqrt (v : ℝ)
  have hs2 : σ ^ 2 = (v : ℝ) := Real.sq_sqrt v.coe_nonneg
  have hsnonneg : 0 ≤ σ := Real.sqrt_nonneg _
  have hσlo : S * r ≤ σ := by nlinarith [mul_pos hS hr]
  have hupper : (v : ℝ) ≤ (S + 1) ^ 2 * r ^ 2 :=
    hhi.trans (mul_le_mul_of_nonneg_right (by nlinarith : S ^ 2 + 1 ≤ (S + 1) ^ 2)
      (sq_nonneg r))
  have hσhi : σ ≤ (S + 1) * r := by
    apply le_of_sq_le_sq _ (by positivity)
    simpa only [mul_pow, hs2] using hupper
  have hσ : 0 < σ := lt_of_lt_of_le (mul_pos hS hr) hσlo
  have hnn : NNReal.mk (σ ^ 2) (sq_nonneg σ) = v := NNReal.eq hs2
  have hB : (∫ x, x ^ 2 ∂(μ : Measure ℝ)) ≤ (S + 1) ^ 2 * r ^ 2 := by
    rw [hmoment]
    exact hupper
  have hWσ : wasserstein1 μ (centeredGaussian (NNReal.mk (σ ^ 2) (sq_nonneg σ)))
      (integrable_id_of_secondMoment μ hμ2) (integrable_id_centeredGaussian _) < η * r := by
    have h := hW.trans_lt (show gaussianApproximationConstant * (δ * r) < η * r by
      simpa only [mul_assoc, K] using mul_lt_mul_of_pos_right hKδ hr)
    simpa only [wasserstein1, hnn] using h
  have hclose := hcont r σ hr ⟨hσlo, hσhi⟩ μ hμ2 hmean hB hWσ
  have hlargeunit := hlarge (σ / r) ((le_div_iff₀ hr).mpr hσlo)
  have hscale := entropyBetween_normalize
    (centeredGaussian (NNReal.mk (σ ^ 2) (sq_nonneg σ))) hr.ne' one_ne_zero hC.ne'
  rw [normalize_centeredGaussian] at hscale
  rw [hscale] at hlargeunit
  simp only [mul_one, mul_comm r C] at hlargeunit
  have hlow := (abs_lt.mp hclose).1
  linarith

end ExactOverlaps.GaussianEntropyGrowth
