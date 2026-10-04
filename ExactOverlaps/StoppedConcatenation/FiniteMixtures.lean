/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.ConvolutionDisintegration.Convexity
public import ExactOverlaps.Entropy.Finite

/-! Actual finite probability mixtures, including zero weights. -/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ExactOverlaps.ConvolutionDisintegration

variable {ι α : Type*} [Fintype ι] [MeasurableSpace α]

def finiteMix (p : PMF ι) (μ : ι → ProbabilityMeasure α) : ProbabilityMeasure α :=
  ⟨∑ i, p i • (μ i : Measure α), ⟨by
    rw [Measure.finsetSum_apply]
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    simpa only [tsum_fintype] using p.tsum_coe⟩⟩

omit [Fintype ι] in
theorem kernel_comp_finite_sum {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (κ : Kernel β γ) (μ : ι → Measure β) (s : Finset ι) :
    κ ∘ₘ (∑ i ∈ s, μ i) = ∑ i ∈ s, κ ∘ₘ μ i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, Measure.comp_add, ih]

theorem mixture_finiteMix (p : PMF ι) (θ : ι → ProbabilityMeasure FactorFamily) :
    mixture (finiteMix p θ) = finiteMix p (fun i ↦ mixture (θ i)) := by
  apply Subtype.ext
  change convolutionKernel ∘ₘ (∑ i, p i • (θ i : Measure FactorFamily)) = _
  rw [kernel_comp_finite_sum]
  simp only [Measure.comp_smul]
  rfl

theorem averageCost_finiteMix (p : PMF ι) (θ : ι → ProbabilityMeasure FactorFamily) (r : ℝ) :
    averageCost r (finiteMix p θ) = ∑ i, (p i).toReal * averageCost r (θ i) := by
  change (∫ c, cost r c ∂(∑ i, p i • (θ i : Measure FactorFamily))) = _
  rw [integral_finsetSum_measure
    (fun i _ ↦ (integrable_cost r (θ i)).smul_measure (p.apply_ne_top i))]
  simp only [integral_smul_measure, smul_eq_mul]
  rfl

end ExactOverlaps.ConvolutionDisintegration
