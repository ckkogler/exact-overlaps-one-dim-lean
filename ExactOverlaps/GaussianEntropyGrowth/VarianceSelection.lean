/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic

/-!
# Selecting a finite variance block

If the total variance reaches a positive target and each summand is at
most d, some deterministic subset reaches the target with excess at most
d. The construction needs no ordering or positivity of individual weights.
-/

@[expose] public section

namespace ExactOverlaps.GaussianEntropyGrowth

lemma exists_subset_sum_between {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    {A d : ℝ} (hA : 0 < A) (hw : ∀ i ∈ s, w i ≤ d)
    (hs : A ≤ ∑ i ∈ s, w i) :
    ∃ t : Finset ι, t ⊆ s ∧ A ≤ ∑ i ∈ t, w i ∧ (∑ i ∈ t, w i) ≤ A + d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty] at hs; linarith
  | @insert a s ha ih =>
    by_cases hsmall : A ≤ ∑ i ∈ s, w i
    · obtain ⟨t, ht, hlo, hhi⟩ := ih (fun i hi ↦ hw i (Finset.mem_insert_of_mem hi)) hsmall
      exact ⟨t, ht.trans (Finset.subset_insert _ _), hlo, hhi⟩
    · refine ⟨insert a s, Finset.Subset.refl _, hs, ?_⟩
      rw [Finset.sum_insert ha]
      have hwa := hw a (Finset.mem_insert_self _ _)
      linarith

end ExactOverlaps.GaussianEntropyGrowth
