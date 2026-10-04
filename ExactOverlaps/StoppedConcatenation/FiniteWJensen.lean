/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.FiniteMixtures

/-! Convexity of W for every actual finite probability mixture. -/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ExactOverlaps.ConvolutionDisintegration

variable {ι : Type*} [Fintype ι]

theorem IsDisintegration.finiteMix (p : PMF ι) (μ : ι → ProbabilityMeasure ℝ)
    (θ : ι → ProbabilityMeasure FactorFamily) (r : ℝ)
    (h : ∀ i, IsDisintegration (μ i) r (θ i)) :
    IsDisintegration (finiteMix p μ) r (finiteMix p θ) := by
  constructor
  · rw [mixture_finiteMix]
    congr 1
    funext i
    exact (h i).1
  · change ∀ᵐ c ∂(∑ i, p i • (θ i : Measure FactorFamily)), Admissible r c
    rw [ae_finsetSum_measure_iff]
    intro i _
    exact Measure.ae_smul_measure (h i).2 _

theorem W_finiteMix_le (p : PMF ι) (μ : ι → ProbabilityMeasure ℝ)
    {r : ℝ} (hr : 0 ≤ r) :
    W (finiteMix p μ) r ≤ ∑ i, (p i).toReal * W (μ i) r := by
  classical
  apply le_of_forall_pos_le_add
  intro ε hε
  choose θ hθ hc using fun i ↦ exists_cost_lt hr (μ i) hε
  have h := W_le_averageCost (IsDisintegration.finiteMix p μ θ r hθ)
  rw [averageCost_finiteMix] at h
  calc
    _ ≤ ∑ i, (p i).toReal * averageCost r (θ i) := h
    _ ≤ ∑ i, (p i).toReal * (W (μ i) r + ε) :=
      Finset.sum_le_sum (fun i _ ↦ mul_le_mul_of_nonneg_left (hc i).le ENNReal.toReal_nonneg)
    _ = (∑ i, (p i).toReal * W (μ i) r) + ε := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
        Entropy.sum_pmf_toReal, one_mul]

end ExactOverlaps.ConvolutionDisintegration
