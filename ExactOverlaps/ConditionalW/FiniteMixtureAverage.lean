/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.Entropy.JointMixture
public import ExactOverlaps.Probability.FiberAverages

/-! Finite expectations for genuine discrete kernel mixtures. -/

@[expose] public section

open scoped Classical ENNReal BigOperators

namespace ExactOverlaps.ConditionalW

open Entropy FiniteProbability

theorem expectation_eq_sum_of_support_subset {α : Type*} (p : PMF α)
    (hp : p.support.Finite) (s : Finset α) (hs : p.support ⊆ s) (F : α → ℝ) :
    expectation p hp F = ∑ a ∈ s, (p a).toReal * F a := by
  unfold expectation
  apply Finset.sum_subset
  · intro a ha
    exact hs (by simpa using ha)
  · intro a _ ha
    have hz : p a = 0 := by simpa using ha
    simp [hz]

theorem jointMixture_support_finite_of_finite {α β : Type*}
    (p : PMF α) (hp : p.support.Finite) (k : α → PMF β)
    (hk : ∀ a, (k a).support.Finite) : (jointMixture p k).support.Finite := by
  let s : Finset β := hp.toFinset.biUnion (fun a ↦ (hk a).toFinset)
  apply (hp.toFinset ×ˢ s).finite_toSet.subset
  rintro ⟨a, b⟩ hab
  have hne : p a * k a b ≠ 0 := by
    simpa only [PMF.mem_support_iff, jointMixture_apply] using hab
  have ha : a ∈ p.support := left_ne_zero_of_mul hne
  have hb : b ∈ (k a).support := right_ne_zero_of_mul hne
  exact Finset.mem_product.mpr ⟨by simpa using ha,
    Finset.mem_biUnion.mpr ⟨a, by simpa using ha, by simpa using hb⟩⟩

theorem expectation_jointMixture {α β : Type*}
    (p : PMF α) (hp : p.support.Finite) (k : α → PMF β)
    (hk : ∀ a, (k a).support.Finite) (F : α × β → ℝ) :
    expectation (jointMixture p k) (jointMixture_support_finite_of_finite p hp k hk) F =
      expectation p hp (fun a ↦ expectation (k a) (hk a) (fun b ↦ F (a, b))) := by
  let s : Finset β := hp.toFinset.biUnion (fun a ↦ (hk a).toFinset)
  have hks (a : α) (ha : a ∈ p.support) : (k a).support ⊆ s := by
    intro b hb
    exact Finset.mem_biUnion.mpr ⟨a, by simpa using ha, by simpa using hb⟩
  have hjs : (jointMixture p k).support ⊆
      (↑(hp.toFinset ×ˢ s : Finset (α × β)) : Set (α × β)) := by
    rintro ⟨a, b⟩ hab
    have hne : p a * k a b ≠ 0 := by
      simpa only [PMF.mem_support_iff, jointMixture_apply] using hab
    have ha : a ∈ p.support := left_ne_zero_of_mul hne
    have hb : b ∈ (k a).support := right_ne_zero_of_mul hne
    exact Finset.mem_product.mpr ⟨by simpa using ha, hks a ha hb⟩
  rw [expectation_eq_sum_of_support_subset _ _ _ hjs, Finset.sum_product]
  change (∑ a ∈ hp.toFinset, _) = ∑ a ∈ hp.toFinset, _
  apply Finset.sum_congr rfl
  intro a ha
  dsimp only
  rw [expectation_eq_sum_of_support_subset (k a) (hk a) s (hks a (by simpa using ha))]
  simp only [jointMixture_apply, ENNReal.toReal_mul, mul_assoc, Finset.mul_sum]

end ExactOverlaps.ConditionalW
