module

public import ExactOverlaps.Probability.FiniteMoments
import Mathlib.Data.Finset.Max

/-!
# Cumulative masses and finite stochastic domination

The cumulative mass of a finite real statistic is its actual indicator
expectation. Evaluating this distribution function at the statistic gives
the finite stochastic domination of a uniform variable used in the
cumulative-entropy estimate.
-/

@[expose] public section

open scoped BigOperators ENNReal Classical

namespace ExactOverlaps.FiniteProbability

noncomputable def cumulativeMass {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (x : α → ℝ) (a : ℝ) : ℝ := expectation p hp (fun z ↦ if x z ≤ a then 1 else 0)

lemma cumulativeMass_nonneg {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (x : α → ℝ) (a : ℝ) : 0 ≤ cumulativeMass p hp x a := by
  exact expectation_nonneg p hp (fun _ _ ↦ by split_ifs <;> norm_num)

lemma cumulativeMass_le_one {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (x : α → ℝ) (a : ℝ) : cumulativeMass p hp x a ≤ 1 := by
  rw [← expectation_const p hp 1]
  exact expectation_mono p hp (fun _ _ ↦ by split_ifs <;> norm_num)

lemma cumulativeMass_mono {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (x : α → ℝ) : Monotone (cumulativeMass p hp x) := by
  intro a b hab
  apply expectation_mono p hp
  intro z _
  by_cases hza : x z ≤ a
  · simp [hza, hza.trans hab]
  · simp only [hza, ite_false]
    split_ifs <;> norm_num

lemma one_sub_cumulativeMass {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (x : α → ℝ) (a : ℝ) :
    1 - cumulativeMass p hp x a = expectation p hp (fun z ↦ if a < x z then 1 else 0) := by
  have he : 1 - cumulativeMass p hp x a =
      expectation p hp (fun z ↦ 1 - (if x z ≤ a then 1 else 0)) := by
    rw [expectation_sub, expectation_const]
    rfl
  rw [he]
  unfold expectation
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : x z ≤ a
  · simp [hz, not_lt.mpr hz]
  · simp [hz, lt_of_not_ge hz]

lemma cumulativeMass_eq_sum_filter {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (x : α → ℝ) (a : ℝ) : cumulativeMass p hp x a =
      ∑ z ∈ hp.toFinset.filter (fun z ↦ x z ≤ a), (p z).toReal := by
  simp [cumulativeMass, expectation, Finset.sum_filter]

lemma cumulativeMass_lower_event {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (x : α → ℝ) {u : ℝ} (hu : 0 ≤ u) :
    expectation p hp (fun z ↦ if cumulativeMass p hp x (x z) ≤ u then 1 else 0) ≤ u := by
  let s := hp.toFinset.filter (fun z ↦ cumulativeMass p hp x (x z) ≤ u)
  have he : expectation p hp (fun z ↦ if cumulativeMass p hp x (x z) ≤ u then 1 else 0) =
      ∑ z ∈ s, (p z).toReal := by
    simp [s, expectation, Finset.sum_filter]
  rw [he]
  by_cases hs : s.Nonempty
  · obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image s x hs
    have hau : cumulativeMass p hp x (x a) ≤ u := (Finset.mem_filter.mp ha).2
    apply le_trans _ hau
    rw [cumulativeMass_eq_sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro z hz
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1, hmax z hz⟩
    · intro _ _ _
      exact ENNReal.toReal_nonneg
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp hs
    simpa [hempty] using hu

lemma cumulativeMass_shift_lower_event {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (x : α → ℝ) {r u : ℝ} (hr : 0 ≤ r) (hu : 0 ≤ u) :
    expectation p hp (fun z ↦ if cumulativeMass p hp x (x z + r) ≤ u then 1 else 0) ≤ u := by
  apply le_trans _ (cumulativeMass_lower_event p hp x hu)
  apply expectation_mono p hp
  intro z _
  have hm := cumulativeMass_mono p hp x (show x z ≤ x z + r by linarith)
  by_cases hz : cumulativeMass p hp x (x z + r) ≤ u
  · simp [hz, hm.trans hz]
  · simp only [hz, ite_false]
    split_ifs <;> norm_num

end ExactOverlaps.FiniteProbability
