module

public import ExactOverlaps.Probability.FiniteCDF

/-!
# Atom witnesses for strictly positive cumulative probabilities

A positive atom below a cut witnesses positive cumulative mass. A positive
atom above it witnesses positive complementary mass. These facts validate
the product predictor on every event that actually occurs.
-/

@[expose] public section

open scoped BigOperators ENNReal Classical

namespace ExactOverlaps.FiniteProbability

lemma atom_le_indicator_expectation {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (P : α → Prop) (a : α) (ha : P a) :
    (p a).toReal ≤ expectation p hp (fun z ↦ if P z then 1 else 0) := by
  by_cases hs : a ∈ p.support
  · calc
      (p a).toReal = (p a).toReal * (if P a then 1 else 0) := by simp [ha]
      _ ≤ _ := by
        unfold expectation
        exact Finset.single_le_sum (f := fun z ↦ (p z).toReal * (if P z then 1 else 0))
          (s := hp.toFinset) (a := a)
          (fun z _ ↦ by split_ifs <;> positivity) (by simpa using hs)
  · have hz : p a = 0 := by simpa using hs
    rw [hz, ENNReal.toReal_zero]
    exact expectation_nonneg p hp (fun _ _ ↦ by split_ifs <;> norm_num)

lemma atom_le_cumulativeMass {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (x : α → ℝ) (a : α) {b : ℝ} (hab : x a ≤ b) :
    (p a).toReal ≤ cumulativeMass p hp x b :=
  atom_le_indicator_expectation p hp (fun z ↦ x z ≤ b) a hab

lemma atom_le_one_sub_cumulativeMass {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (x : α → ℝ) (a : α) {b : ℝ} (hba : b < x a) :
    (p a).toReal ≤ 1 - cumulativeMass p hp x b := by
  rw [one_sub_cumulativeMass]
  exact atom_le_indicator_expectation p hp (fun z ↦ b < x z) a hba

lemma cumulativeMass_pos_of_atom_le {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (x : α → ℝ) (a : α) (ha : a ∈ p.support) {b : ℝ} (hab : x a ≤ b) :
    0 < cumulativeMass p hp x b := by
  exact (ENNReal.toReal_pos (by simpa using ha) (p.apply_ne_top a)).trans_le
    (atom_le_cumulativeMass p hp x a hab)

lemma cumulativeMass_lt_one_of_lt_atom {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (x : α → ℝ) (a : α) (ha : a ∈ p.support) {b : ℝ} (hba : b < x a) :
    cumulativeMass p hp x b < 1 := by
  have h := (ENNReal.toReal_pos (by simpa using ha) (p.apply_ne_top a)).trans_le
    (atom_le_one_sub_cumulativeMass p hp x a hba)
  linarith

end ExactOverlaps.FiniteProbability
