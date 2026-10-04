/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.GaussianEntropyGrowth.SubsumConvolution
public import ExactOverlaps.GaussianEntropyGrowth.VarianceSelection
public import ExactOverlaps.GaussianEntropyGrowth.VarianceBand

/-!
# Entropy growth of bounded independent centered sums

The constants depend only on the integer scale ratio and the desired
entropy error. A deterministic variance block is approximated by a
Gaussian; convolution monotonicity restores the remaining summands.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

universe u v

namespace ExactOverlaps.GaussianEntropyGrowth

open GaussianApproximation GaussianScaleEntropy

/-- Primary Lemma 3.9, uniformly over actual independent random variables. -/
theorem bounded_independent_sum_entropy_growth (C : ℕ) (hC : 1 < C)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∃ A > 0,
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        {ι : Type v} [Fintype ι] (r : ℝ), 0 < r →
      ∀ (X : ι → Ω → ℝ), (∀ i, AEMeasurable (X i) μ) → iIndepFun X μ →
      (∀ i, (∫ ω, X i ω ∂μ) = 0) →
      (∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ δ * r) →
      A * r ^ 2 ≤ ∑ i, variance (X i) μ →
      Real.log (C : ℝ) - ε < entropyBetween (sumLaw μ X Finset.univ) r ((C : ℝ) * r) := by
  have hCpos : 0 < (C : ℝ) := by exact_mod_cast (lt_trans Nat.zero_lt_one hC)
  obtain ⟨δ, hδ, A, hA, hδ1, hband⟩ := entropy_growth_variance_band hCpos hε
  refine ⟨δ, hδ, A, hA, ?_⟩
  intro Ω _ μ _ ι _ r hr X hX hind hmean hR htotal
  classical
  let w : ι → ℝ := fun i ↦ ∫ ω, (X i ω) ^ 2 ∂μ
  have hw (i : ι) : w i ≤ (δ * r) ^ 2 := secondMoment_le_of_ae_bounded μ (hX i) (hR i)
  have hw0 (i : ι) : 0 ≤ w i := integral_nonneg (fun ω ↦ sq_nonneg (X i ω))
  have hvar (i : ι) : variance (X i) μ = w i := by
    rw [variance_eq_integral (hX i), hmean i]
    simp only [sub_zero, w]
  have hsum : A * r ^ 2 ≤ ∑ i, w i := by simpa only [hvar] using htotal
  obtain ⟨s, hs, hslo, hshi⟩ := exists_subset_sum_between Finset.univ w
    (mul_pos hA (sq_pos_of_pos hr)) (fun i _ ↦ hw i) hsum
  have hv0 : 0 ≤ ∑ i ∈ s, w i := Finset.sum_nonneg (fun i _ ↦ hw0 i)
  let q := NNReal.mk (∑ i ∈ s, w i) hv0
  have hq : 0 < (q : ℝ) := lt_of_lt_of_le (mul_pos hA (sq_pos_of_pos hr)) hslo
  have hδsq : δ ^ 2 ≤ 1 := by nlinarith
  have hupper : (q : ℝ) ≤ (A + 1) * r ^ 2 := by
    have hprod := mul_le_mul_of_nonneg_right hδsq (sq_nonneg r)
    change (∑ i ∈ s, w i) ≤ (A + 1) * r ^ 2
    nlinarith
  have hμ2 := integrable_sq_sumLaw μ X s (fun i _ ↦ hX i) (fun i _ ↦ hR i)
  have hm := mean_sumLaw μ X s (fun i _ ↦ hX i) (fun i _ ↦ hR i) (fun i _ ↦ hmean i)
  have hm2 : (∫ x, x ^ 2 ∂(sumLaw μ X s : Measure ℝ)) = (q : ℝ) :=
    secondMoment_sumLaw μ X s (fun i _ ↦ hX i) hind (fun i _ ↦ hR i) (fun i _ ↦ hmean i)
  have hW := wasserstein1_subsum_le μ X s hX hind hmean hR q hq rfl
  have hgrowth := hband r hr (sumLaw μ X s) hμ2 q hm hm2 hslo hupper hW
  exact hgrowth.trans_le (entropyBetween_subsum_le μ X s Finset.univ hs hX hind hR hr C
    (lt_trans Nat.zero_lt_one hC))

end ExactOverlaps.GaussianEntropyGrowth
