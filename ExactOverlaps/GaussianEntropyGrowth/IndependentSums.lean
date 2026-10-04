/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.GaussianEntropyGrowth.TranslationMixture
public import ExactOverlaps.GaussianApproximation.BoundedSumApproximation

/-!
# Actual laws of bounded independent subsums

Every law here is the pushforward from the original probability space.
Finite subsums have the required moments and support bounds. Disjoint
subsets yield independent sums and hence genuine convolution of their laws.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace ExactOverlaps.GaussianEntropyGrowth

open GaussianApproximation GaussianScaleEntropy

variable {Ω ι : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]

def sumLaw (X : ι → Ω → ℝ) (s : Finset ι) : ProbabilityMeasure ℝ :=
  μ.toProbabilityMeasure.map (fun ω ↦ ∑ i ∈ s, X i ω)

lemma sumLaw_toMeasure (X : ι → Ω → ℝ) (s : Finset ι) :
    (sumLaw μ X s : Measure ℝ) = μ.map (fun ω ↦ ∑ i ∈ s, X i ω) := by
  simp only [sumLaw, ProbabilityMeasure.toMeasure_map, Measure.coe_toProbabilityMeasure]

omit [IsProbabilityMeasure μ] in
lemma ae_abs_sum_le (X : ι → Ω → ℝ) (s : Finset ι) {R : ℝ}
    (hR : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω| ≤ R) :
    ∀ᵐ ω ∂μ, |∑ i ∈ s, X i ω| ≤ (s.card : ℝ) * R := by
  classical
  have hall : ∀ᵐ ω ∂μ, ∀ i : s, |X i ω| ≤ R :=
    ae_all_iff.mpr (fun i ↦ hR i i.2)
  filter_upwards [hall] with ω hω
  calc
    _ ≤ ∑ i ∈ s, |X i ω| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ s, R := Finset.sum_le_sum (fun i hi ↦ hω ⟨i, hi⟩)
    _ = _ := by simp

lemma memLp_sum_of_bounded (X : ι → Ω → ℝ) (s : Finset ι)
    (hX : ∀ i ∈ s, AEMeasurable (X i) μ) {R : ℝ}
    (hR : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω| ≤ R) :
    MemLp (fun ω ↦ ∑ i ∈ s, X i ω) 3 μ := by
  apply memLp_three_of_ae_bounded (Finset.aemeasurable_fun_sum s hX)
  exact ae_abs_sum_le μ X s hR

lemma sumLaw_hasBoundedSupport (X : ι → Ω → ℝ) (s : Finset ι)
    (hX : ∀ i ∈ s, AEMeasurable (X i) μ) {R : ℝ}
    (hR : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω| ≤ R) :
    Entropy.HasBoundedSupport (sumLaw μ X s) := by
  refine ⟨-((s.card : ℝ) * R), (s.card : ℝ) * R, ?_⟩
  rw [sumLaw_toMeasure]
  apply (ae_map_iff (Finset.aemeasurable_fun_sum s hX) measurableSet_Icc).mpr
  exact (ae_abs_sum_le μ X s hR).mono (fun _ hω ↦ abs_le.mp hω)

lemma integrable_sq_sumLaw (X : ι → Ω → ℝ) (s : Finset ι)
    (hX : ∀ i ∈ s, AEMeasurable (X i) μ) {R : ℝ}
    (hR : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω| ≤ R) :
    Integrable (fun x : ℝ ↦ x ^ 2) (sumLaw μ X s : Measure ℝ) := by
  have hS := memLp_sum_of_bounded μ X s hX hR
  rw [sumLaw_toMeasure]
  apply (integrable_map_measure
    (show Measurable (fun x : ℝ ↦ x ^ 2) by fun_prop).aestronglyMeasurable
    hS.aemeasurable).mpr
  exact integrable_sq_of_memLp_three hS

lemma mean_sumLaw (X : ι → Ω → ℝ) (s : Finset ι)
    (hX : ∀ i ∈ s, AEMeasurable (X i) μ) {R : ℝ}
    (hR : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω| ≤ R)
    (hmean : ∀ i ∈ s, (∫ ω, X i ω ∂μ) = 0) :
    (∫ x, x ∂(sumLaw μ X s : Measure ℝ)) = 0 := by
  rw [sumLaw_toMeasure, integral_map (f := fun x : ℝ ↦ x)
    (Finset.aemeasurable_fun_sum s hX) measurable_id.aestronglyMeasurable]
  rw [integral_finsetSum _ (fun i hi ↦ integrable_of_memLp_three
    (memLp_three_of_ae_bounded (hX i hi) (hR i hi)))]
  exact Finset.sum_eq_zero hmean

lemma secondMoment_sumLaw (X : ι → Ω → ℝ) (s : Finset ι)
    (hX : ∀ i ∈ s, AEMeasurable (X i) μ) (hind : iIndepFun X μ) {R : ℝ}
    (hR : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω| ≤ R)
    (hmean : ∀ i ∈ s, (∫ ω, X i ω ∂μ) = 0) :
    (∫ x, x ^ 2 ∂(sumLaw μ X s : Measure ℝ)) = ∑ i ∈ s, ∫ ω, (X i ω) ^ 2 ∂μ := by
  have hS := memLp_sum_of_bounded μ X s hX hR
  have hm : (∫ ω, (∑ i ∈ s, X i ω) ∂μ) = 0 := by
    rw [integral_finsetSum _ (fun i hi ↦ integrable_of_memLp_three
      (memLp_three_of_ae_bounded (hX i hi) (hR i hi)))]
    exact Finset.sum_eq_zero hmean
  have hv := IndepFun.variance_sum
    (fun i hi ↦ (memLp_three_of_ae_bounded (hX i hi) (hR i hi)).mono_exponent (by norm_num))
    (fun i _ j _ hij ↦ hind.indepFun hij)
  have hvar : variance (fun ω ↦ ∑ i ∈ s, X i ω) μ =
      ∑ i ∈ s, ∫ ω, (X i ω) ^ 2 ∂μ := by
    have he : (∑ i ∈ s, X i) = (fun ω ↦ ∑ i ∈ s, X i ω) := by
      funext ω
      simp only [Finset.sum_apply]
    rw [he] at hv
    refine hv.trans (Finset.sum_congr rfl (fun i hi ↦ ?_))
    rw [variance_eq_integral (hX i hi), hmean i hi]
    simp only [sub_zero]
  rw [variance_eq_integral hS.aemeasurable, hm] at hvar
  rw [sumLaw_toMeasure, integral_map (Finset.aemeasurable_fun_sum s hX)
    (show Measurable (fun x : ℝ ↦ x ^ 2) by fun_prop).aestronglyMeasurable]
  simpa only [sub_zero] using hvar

end ExactOverlaps.GaussianEntropyGrowth
