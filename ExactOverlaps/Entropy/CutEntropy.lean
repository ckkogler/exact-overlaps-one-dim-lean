module

public import ExactOverlaps.Entropy.BinaryPrediction
public import ExactOverlaps.Probability.FiniteCDF
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Measurability of genuine conditional cut entropy

The cut is a two-valued statistic of a finite law. Its entropy is the sum
of the two continuous negative-mass-log-mass terms of the actual cumulative
mass. Conditional cut entropy averages this formula over positive fibers.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal Classical
open ExactOverlaps.FiniteProbability

namespace ExactOverlaps.Entropy

lemma measurable_cumulativeMass {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (x : α → ℝ) : Measurable (cumulativeMass p hp x) :=
  (cumulativeMass_mono p hp x).measurable

lemma cut_true_mass_eq_cumulativeMass {α : Type*} (p : PMF α)
    (hp : p.support.Finite) (x : α → ℝ) (a : ℝ) :
    ((p.map (fun z ↦ decide (x z ≤ a))) true).toReal = cumulativeMass p hp x a := by
  have h := expectation_map p hp (fun z ↦ decide (x z ≤ a))
    (fun b ↦ if b then (1 : ℝ) else 0)
  rw [expectation_eq_sum_univ] at h
  simpa [Fintype.sum_bool, cumulativeMass] using h

lemma finiteEntropy_cut_eq {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (x : α → ℝ) (a : ℝ) :
    finiteEntropy (p.map (fun z ↦ decide (x z ≤ a)))
        (by simpa using hp.image (fun z ↦ decide (x z ≤ a))) =
      Real.negMulLog (cumulativeMass p hp x a) +
        Real.negMulLog (1 - cumulativeMass p hp x a) := by
  let q := p.map (fun z ↦ decide (x z ≤ a))
  have hs := sum_pmf_toReal q
  simp only [Fintype.sum_bool] at hs
  have ht : (q true).toReal = cumulativeMass p hp x a :=
    cut_true_mass_eq_cumulativeMass p hp x a
  have hf : (q false).toReal = 1 - cumulativeMass p hp x a := by linarith
  rw [finiteEntropy_eq_sum_of_support_subset _ _ Finset.univ
    (fun _ _ ↦ Finset.mem_univ _)]
  change (∑ b : Bool, Real.negMulLog (q b).toReal) = _
  simp only [Fintype.sum_bool, ht, hf]

noncomputable def conditionalCutEntropy {α β : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (x : α → ℝ) (a : ℝ) : ℝ :=
  averageStatisticConditionalEntropy p hp f (fun z ↦ decide (x z ≤ a))

lemma conditionalCutEntropy_nonneg {α β : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (x : α → ℝ) (a : ℝ) :
    0 ≤ conditionalCutEntropy p hp f x a := by
  unfold conditionalCutEntropy averageStatisticConditionalEntropy
  exact Finset.sum_nonneg (fun _ _ ↦ mul_nonneg ENNReal.toReal_nonneg
    (finiteEntropy_nonneg _ _))

lemma measurable_conditionalCutEntropy {α β : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (x : α → ℝ) :
    Measurable (conditionalCutEntropy p hp f x) := by
  unfold conditionalCutEntropy averageStatisticConditionalEntropy
  apply Finset.measurable_sum
  intro b _
  apply Measurable.const_mul
  simp_rw [finiteEntropy_cut_eq (conditionalPMF p f b)
    (conditionalPMF_support_finite p hp f b) x]
  apply Measurable.add
  · exact Real.continuous_negMulLog.measurable.comp (measurable_cumulativeMass _ _ x)
  · exact Real.continuous_negMulLog.measurable.comp
      (measurable_const.sub (measurable_cumulativeMass _ _ x))

end ExactOverlaps.Entropy
