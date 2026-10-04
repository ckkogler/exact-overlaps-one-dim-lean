module

public import ExactOverlaps.Probability.FiniteIntegration
public import ExactOverlaps.Probability.FinitePositiveIntegration

/-!
# Nonnegative integration of finite probability expectations

The integral stays in ENNReal until finiteness is established. The identity
applies on arbitrary measurable spaces and requires hypotheses only on the
actual support of the probability law.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators

namespace ExactOverlaps.FiniteProbability

lemma lintegral_ofReal_expectation {Ω α : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : PMF α) (hp : p.support.Finite) (F : Ω → α → ℝ)
    (hm : ∀ a ∈ p.support, Measurable (fun ω ↦ F ω a))
    (hn : ∀ a ∈ p.support, ∀ ω, 0 ≤ F ω a) :
    (∫⁻ ω, ENNReal.ofReal (expectation p hp (F ω)) ∂μ) =
      ∑ a ∈ hp.toFinset, p a * ∫⁻ ω, ENNReal.ofReal (F ω a) ∂μ := by
  calc
    (∫⁻ ω, ENNReal.ofReal (expectation p hp (F ω)) ∂μ) =
        ∫⁻ ω, ∑ a ∈ hp.toFinset, p a * ENNReal.ofReal (F ω a) ∂μ := by
      apply lintegral_congr
      intro ω
      unfold expectation
      rw [ENNReal.ofReal_sum_of_nonneg
        (fun a ha ↦ mul_nonneg ENNReal.toReal_nonneg (hn a (by simpa using ha) ω))]
      apply Finset.sum_congr rfl
      intro a _
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (p.apply_ne_top a)]
    _ = _ := by
      rw [lintegral_finsetSum _ (fun a ha ↦
        ((hm a (by simpa using ha)).ennreal_ofReal).const_mul _)]
      apply Finset.sum_congr rfl
      intro a _
      exact lintegral_const_mul' _ _ (p.apply_ne_top a)

lemma measurable_expectation {Ω α : Type*} [MeasurableSpace Ω]
    (p : PMF α) (hp : p.support.Finite) (F : Ω → α → ℝ)
    (hm : ∀ a ∈ p.support, Measurable (fun ω ↦ F ω a)) :
    Measurable (fun ω ↦ expectation p hp (F ω)) := by
  exact Finset.measurable_sum _ (fun a ha ↦ (hm a (by simpa using ha)).const_mul _)

end ExactOverlaps.FiniteProbability
