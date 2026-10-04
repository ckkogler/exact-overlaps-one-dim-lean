/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.GaussianEntropyGrowth.IndependentSums
public import ExactOverlaps.GaussianScaleEntropy.GaussianMoments

/-!
# Convolution and Gaussian approximation for actual subsums

Disjoint independent coordinate blocks produce the convolution of their
actual laws. This transfers the entropy monotonicity and Gaussian
approximation estimates to any deterministic finite subset of coordinates.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace ExactOverlaps.GaussianEntropyGrowth

open GaussianApproximation GaussianScaleEntropy

variable {Ω ι : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
lemma independent_subsums (X : ι → Ω → ℝ) (s t : Finset ι)
    (hst : Disjoint s t) (hX : ∀ i, AEMeasurable (X i) μ) (hind : iIndepFun X μ) :
    IndepFun (fun ω ↦ ∑ i ∈ s, X i ω) (fun ω ↦ ∑ i ∈ t, X i ω) μ := by
  have h := iIndepFun.indepFun_finset₀ s t hst hind hX
  have hs : Measurable (fun w : s → ℝ ↦ ∑ i, w i) := by fun_prop
  have ht : Measurable (fun w : t → ℝ ↦ ∑ i, w i) := by fun_prop
  have hc := h.comp hs ht
  have hse : (fun ω ↦ ∑ i : s, X i ω) = (fun ω ↦ ∑ i ∈ s, X i ω) :=
    funext (fun ω ↦ Finset.sum_attach s (fun i ↦ X i ω))
  have hte : (fun ω ↦ ∑ i : t, X i ω) = (fun ω ↦ ∑ i ∈ t, X i ω) :=
    funext (fun ω ↦ Finset.sum_attach t (fun i ↦ X i ω))
  change IndepFun (fun ω ↦ ∑ i : s, X i ω) (fun ω ↦ ∑ i : t, X i ω) μ at hc
  rwa [hse, hte] at hc

lemma sumLaw_union [DecidableEq ι] (X : ι → Ω → ℝ) (s t : Finset ι)
    (hst : Disjoint s t) (hX : ∀ i, AEMeasurable (X i) μ) (hind : iIndepFun X μ) :
    sumLaw μ X (s ∪ t) = Entropy.realConvolution (sumLaw μ X s) (sumLaw μ X t) := by
  classical
  have hs := Finset.aemeasurable_fun_sum s (fun i _ ↦ hX i)
  have ht := Finset.aemeasurable_fun_sum t (fun i _ ↦ hX i)
  have hi := independent_subsums μ X s t hst hX hind
  apply ProbabilityMeasure.toMeasure_injective
  rw [Entropy.realConvolution_toMeasure, sumLaw_toMeasure, sumLaw_toMeasure,
    sumLaw_toMeasure, ← hi.map_add_eq_map_conv_map₀ hs ht]
  congr 1
  funext ω
  exact Finset.sum_union hst

lemma entropyBetween_subsum_le (X : ι → Ω → ℝ) (s t : Finset ι)
    (hst : s ⊆ t) (hX : ∀ i, AEMeasurable (X i) μ) (hind : iIndepFun X μ)
    {R : ℝ} (hR : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ R)
    {r : ℝ} (hr : 0 < r) (C : ℕ) (hC : 0 < C) :
    entropyBetween (sumLaw μ X s) r ((C : ℝ) * r) ≤
      entropyBetween (sumLaw μ X t) r ((C : ℝ) * r) := by
  classical
  have hd : Disjoint s (t \ s) := by
    apply Finset.disjoint_left.mpr
    intro i hi hit
    exact (Finset.mem_sdiff.mp hit).2 hi
  have he := sumLaw_union μ X s (t \ s) hd hX hind
  rw [Finset.union_sdiff_of_subset hst] at he
  rw [he]
  exact entropyBetween_convolution_le (sumLaw μ X s) (sumLaw μ X (t \ s))
    (sumLaw_hasBoundedSupport μ X s (fun i _ ↦ hX i) (fun i _ ↦ hR i))
    (sumLaw_hasBoundedSupport μ X (t \ s) (fun i _ ↦ hX i) (fun i _ ↦ hR i)) hr C hC

lemma wasserstein1_subsum_le (X : ι → Ω → ℝ) (s : Finset ι)
    (hX : ∀ i, AEMeasurable (X i) μ) (hind : iIndepFun X μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = 0) {R : ℝ}
    (hR : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ R) (v : ℝ≥0) (hv : 0 < (v : ℝ))
    (hvariance : (∑ i ∈ s, ∫ ω, (X i ω) ^ 2 ∂μ) = (v : ℝ)) :
    wasserstein1 (sumLaw μ X s) (centeredGaussian v)
      (integrable_id_of_secondMoment _
        (integrable_sq_sumLaw μ X s (fun i _ ↦ hX i) (fun i _ ↦ hR i)))
      (integrable_id_centeredGaussian v) ≤ gaussianApproximationConstant * R := by
  have hv' : (∑ i : s, ∫ ω, (X i ω) ^ 2 ∂μ) = (v : ℝ) := by
    exact (Finset.sum_attach s (fun i ↦ ∫ ω, (X i ω) ^ 2 ∂μ)).trans hvariance
  have hlaw : (sumLaw μ X s : Measure ℝ) = μ.map (fun ω ↦ ∑ i : s, X i ω) := by
    rw [sumLaw_toMeasure]
    congr 1
    funext ω
    exact (Finset.sum_attach s (fun i ↦ X i ω)).symm
  exact wasserstein1_sum_le_of_bounded (fun i : s ↦ X i)
    (fun i ↦ memLp_three_of_ae_bounded (hX i) (hR i)) (hind.restrict s)
    (fun i ↦ hmean i) v hv hv' (sumLaw μ X s) hlaw (fun i ↦ hR i)

lemma secondMoment_le_of_ae_bounded {X : Ω → ℝ} (hX : AEMeasurable X μ)
    {R : ℝ} (hR : ∀ᵐ ω ∂μ, |X ω| ≤ R) :
    (∫ ω, (X ω) ^ 2 ∂μ) ≤ R ^ 2 := by
  have hi := integral_mono_ae
    (integrable_sq_of_memLp_three (memLp_three_of_ae_bounded hX hR)) (integrable_const (R ^ 2))
    (hR.mono (fun ω hω ↦ by nlinarith [sq_abs (X ω), abs_nonneg (X ω)]))
  simpa using hi

end ExactOverlaps.GaussianEntropyGrowth
