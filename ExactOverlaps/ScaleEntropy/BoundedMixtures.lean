/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.ScaleEntropy.Concavity

/-!
# Closure of bounded laws under finite mixtures

A finite collection of almost-sure support intervals has common lower and
upper bounds. The actual mixture measure is carried by that same interval,
including when some component weights are zero.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical

namespace ExactOverlaps.ScaleEntropy

open Entropy

lemma exists_common_support_interval {ι : Type*} [Fintype ι]
    (ν : ι → ProbabilityMeasure ℝ) (hν : ∀ i, HasBoundedSupport (ν i)) :
    ∃ a b : ℝ, ∀ i, ∀ᵐ x ∂(ν i : Measure ℝ), x ∈ Icc a b := by
  choose a b hab using hν
  obtain ⟨A, hA⟩ := (Set.finite_range a).bddBelow
  obtain ⟨B, hB⟩ := (Set.finite_range b).bddAbove
  refine ⟨A, B, fun i ↦ ?_⟩
  filter_upwards [hab i] with x hx
  exact ⟨(hA ⟨i, rfl⟩).trans hx.1, hx.2.trans (hB ⟨i, rfl⟩)⟩

lemma hasBoundedSupport_of_finite_mixture {ι : Type*} [Fintype ι]
    (p : PMF ι) (ν : ι → ProbabilityMeasure ℝ) (hν : ∀ i, HasBoundedSupport (ν i))
    (μ : ProbabilityMeasure ℝ)
    (hmix : (μ : Measure ℝ) = ∑ i, p i • (ν i : Measure ℝ)) : HasBoundedSupport μ := by
  obtain ⟨a, b, hab⟩ := exists_common_support_interval ν hν
  refine ⟨a, b, ?_⟩
  rw [ae_iff, hmix, Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [Measure.smul_apply, ae_iff.mp (hab i), smul_zero]

end ExactOverlaps.ScaleEntropy
