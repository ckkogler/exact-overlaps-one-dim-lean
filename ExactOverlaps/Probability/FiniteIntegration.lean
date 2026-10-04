/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
Adapted from the LpSelfSimilar probability library.
-/
module

public import ExactOverlaps.Probability.FiniteMoments

@[expose] public section

/-!
Interchanging integration with a finite probability expectation. Integrability
is required only on the finite support, so null atoms cause no side conditions.
-/

open MeasureTheory

namespace ExactOverlaps.FiniteProbability

lemma integrable_expectation {Ω α : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (p : PMF α) (hp : p.support.Finite) (F : Ω → α → ℝ)
    (hF : ∀ a ∈ p.support, Integrable (fun ω ↦ F ω a) μ) :
    Integrable (fun ω ↦ expectation p hp (F ω)) μ := by
  apply integrable_finsetSum
  intro a ha
  exact (hF a (by simpa using ha)).const_mul _

lemma integral_expectation {Ω α : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (p : PMF α) (hp : p.support.Finite) (F : Ω → α → ℝ)
    (hF : ∀ a ∈ p.support, Integrable (fun ω ↦ F ω a) μ) :
    (∫ ω, expectation p hp (F ω) ∂μ) = expectation p hp (fun a ↦ ∫ ω, F ω a ∂μ) := by
  unfold expectation
  rw [integral_finsetSum hp.toFinset (fun a ha ↦ (hF a (by simpa using ha)).const_mul _)]
  simp_rw [integral_const_mul]

end ExactOverlaps.FiniteProbability
