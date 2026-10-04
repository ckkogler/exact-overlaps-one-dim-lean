/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.GaussianScaleEntropy.Envelope
public import ExactOverlaps.GaussianScaleEntropy.UniformSum
public import ExactOverlaps.GaussianApproximation.HalfOpenCDF

/-!
# Uniform entropy continuity at unit scale

The comparison law has a uniformly Lipschitz CDF, and both laws satisfy
the same second-moment bound. The genuine Kantorovich dual distance
controls every half-open cell, including boundary atoms of the first law.
The resulting entropy estimate is uniform over physical translations.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace ExactOverlaps.GaussianScaleEntropy

open GaussianApproximation

lemma unit_cellProbability (μ : ProbabilityMeasure ℝ) (t : ℝ) (k : ℤ) :
    (ScaleEntropy.law μ 1 t k).toReal =
      (μ : Measure ℝ).real (Ico ((k : ℝ) - t) ((k : ℝ) + 1 - t)) := by
  rw [ScaleEntropy.law_apply]
  congr 2
  ext x
  simp only [Set.mem_ofPred_eq, ScaleEntropy.quantize, div_one, Int.floor_eq_iff,
    Set.mem_Ico]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

theorem exists_uniform_shiftedEntropy_modulus {B : ℝ} (hB : 0 ≤ B)
    (L : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (μ ν : ProbabilityMeasure ℝ)
      (hμ : Integrable (fun x : ℝ ↦ x) (μ : Measure ℝ))
      (hν : Integrable (fun x : ℝ ↦ x) (ν : Measure ℝ)),
      Integrable (fun x : ℝ ↦ x ^ 2) (μ : Measure ℝ) →
      Integrable (fun x : ℝ ↦ x ^ 2) (ν : Measure ℝ) →
      (∫ x, x ^ 2 ∂(μ : Measure ℝ)) ≤ B →
      (∫ x, x ^ 2 ∂(ν : Measure ℝ)) ≤ B →
      LipschitzWith L (cdf (ν : Measure ℝ)) → wasserstein1 μ ν hμ hν < δ →
      ∀ t ∈ Icc (0 : ℝ) 1, |shiftedEntropy μ 1 t - shiftedEntropy ν 1 t| < ε := by
  obtain ⟨d, hd, hu⟩ := uniform_negMulLog_tsum (summable_entropyEnvelope B) hε
  let e := d / (8 * ((L : ℝ) + 1))
  have he : 0 < e := by dsimp [e]; positivity
  refine ⟨e * d / 8, by positivity, ?_⟩
  intro μ ν hμ hν hμ2 hν2 hμB hνB hL hW t ht
  have hWe : wasserstein1 μ ν hμ hν / e < d / 8 := by
    apply (div_lt_iff₀ he).mpr
    nlinarith [hW]
  have hLe : (L : ℝ) * e ≤ d / 8 := by
    dsimp [e]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < 8 * ((L : ℝ) + 1))).mpr
    nlinarith
  have hcells (k : ℤ) :
      |(ScaleEntropy.law μ 1 t k).toReal - (ScaleEntropy.law ν 1 t k).toReal| < d := by
    rw [unit_cellProbability, unit_cellProbability]
    have h := abs_real_Ico_sub_le_wasserstein1 μ ν hμ hν hL
      ((k : ℝ) - t) ((k : ℝ) + 1 - t) he
    linarith
  have hp (ρ : ProbabilityMeasure ℝ) (k : ℤ) :
      (ScaleEntropy.law ρ 1 t k).toReal ∈ Icc (0 : ℝ) 1 :=
    ⟨ENNReal.toReal_nonneg, by simpa using (ENNReal.toReal_mono ENNReal.one_ne_top
      ((ScaleEntropy.law ρ 1 t).coe_le_one k))⟩
  rw [shiftedEntropy_eq_tsum μ 1 t (summable_cellTerm μ hμ2 hB hμB ht),
    shiftedEntropy_eq_tsum ν 1 t (summable_cellTerm ν hν2 hB hνB ht)]
  exact hu _ _ (hp μ) (hp ν)
    (cellTerm_le_entropyEnvelope μ hμ2 hB hμB ht)
    (cellTerm_le_entropyEnvelope ν hν2 hB hνB ht) hcells

lemma entropy_unit_eq_integral (μ : ProbabilityMeasure ℝ) :
    entropy μ 1 = ∫ t in Ioc (0 : ℝ) 1, shiftedEntropy μ 1 t := by
  rw [entropy, div_one, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

theorem exists_uniform_entropy_modulus {B : ℝ} (hB : 0 ≤ B)
    (L : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (μ ν : ProbabilityMeasure ℝ)
      (hμ : Integrable (fun x : ℝ ↦ x) (μ : Measure ℝ))
      (hν : Integrable (fun x : ℝ ↦ x) (ν : Measure ℝ)),
      Integrable (fun x : ℝ ↦ x ^ 2) (μ : Measure ℝ) →
      Integrable (fun x : ℝ ↦ x ^ 2) (ν : Measure ℝ) →
      (∫ x, x ^ 2 ∂(μ : Measure ℝ)) ≤ B →
      (∫ x, x ^ 2 ∂(ν : Measure ℝ)) ≤ B →
      LipschitzWith L (cdf (ν : Measure ℝ)) → wasserstein1 μ ν hμ hν < δ →
      |entropy μ 1 - entropy ν 1| < ε := by
  obtain ⟨δ, hδ, hu⟩ := exists_uniform_shiftedEntropy_modulus hB L
    (show 0 < ε / 2 by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro μ ν hμ hν hμ2 hν2 hμB hνB hL hW
  have hclose := hu μ ν hμ hν hμ2 hν2 hμB hνB hL hW
  have hiμ : IntegrableOn (shiftedEntropy μ 1) (Ioc (0 : ℝ) 1) :=
    (integrableOn_shiftedEntropy_unit μ hμ2).mono_set Ioc_subset_Icc_self
  have hiν : IntegrableOn (shiftedEntropy ν 1) (Ioc (0 : ℝ) 1) :=
    (integrableOn_shiftedEntropy_unit ν hν2).mono_set Ioc_subset_Icc_self
  rw [entropy_unit_eq_integral, entropy_unit_eq_integral, ← integral_sub hiμ hiν]
  have hbound : (∫ t in Ioc (0 : ℝ) 1, |shiftedEntropy μ 1 t - shiftedEntropy ν 1 t|) ≤
      ∫ _t in Ioc (0 : ℝ) 1, ε / 2 := by
    apply integral_mono_ae (hiμ.sub hiν).abs (integrable_const _)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact (hclose t (Ioc_subset_Icc_self ht)).le
  have hconst : (∫ _t in Ioc (0 : ℝ) 1, ε / 2) = ε / 2 := by simp
  have h := abs_integral_le_integral_abs.trans hbound
  rw [hconst] at h
  linarith

end ExactOverlaps.GaussianScaleEntropy
