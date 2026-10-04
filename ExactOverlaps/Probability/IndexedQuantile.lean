module

public import ExactOverlaps.Probability.FiniteQuantile
public import ExactOverlaps.Probability.FiniteSqrtOdds
public import ExactOverlaps.Entropy.Conditioning

/-!
# Probability-law form of the finite quantile estimate

Finite-index weights extend by zero outside their index range. This turns
the cumulative sequence inequality into a bound for actual PMF expectations.
-/

@[expose] public section

open scoped BigOperators ENNReal Classical

namespace ExactOverlaps.FiniteProbability

lemma expectation_map {α β : Type*} (p : PMF α) (hp : p.support.Finite)
    (f : α → β) (g : β → ℝ) :
    expectation (p.map f) (by simpa using hp.image f) g =
      expectation p hp (fun a ↦ g (f a)) := Entropy.sum_marginal_mul p hp f g

lemma expectation_eq_sum_univ {α : Type*} [Fintype α] (p : PMF α)
    (hp : p.support.Finite) (f : α → ℝ) :
    expectation p hp f = ∑ a, (p a).toReal * f a := by
  unfold expectation
  apply Finset.sum_subset (Finset.subset_univ _)
  intro a _ ha
  have hzero : p a = 0 := by simpa using ha
  simp [hzero]

noncomputable def indexWeight {n : ℕ} (p : PMF (Fin n)) (i : ℕ) : ℝ :=
  if hi : i < n then (p ⟨i, hi⟩).toReal else 0

lemma indexWeight_fin {n : ℕ} (p : PMF (Fin n)) (i : Fin n) :
    indexWeight p i.val = (p i).toReal := by
  unfold indexWeight
  rw [dite_eq_left i.isLt]

lemma indexWeight_nonneg {n : ℕ} (p : PMF (Fin n)) (i : ℕ) : 0 ≤ indexWeight p i := by
  unfold indexWeight
  split_ifs <;> positivity

lemma expectation_eq_sum_range {n : ℕ} (p : PMF (Fin n)) (hp : p.support.Finite)
    (f : ℕ → ℝ) : expectation p hp (fun a ↦ f a.val) =
      ∑ i ∈ Finset.range n, indexWeight p i * f i := by
  rw [expectation_eq_sum_univ]
  have h := Fin.sum_univ_eq_sum_range (fun i ↦ indexWeight p i * f i) n
  simpa only [indexWeight_fin] using h

lemma expectation_lower_half_inv_sqrt_le {n : ℕ} (p : PMF (Fin n))
    (hp : p.support.Finite) (z : ℕ → ℝ)
    (hz : ∀ i < n, (∑ j ∈ Finset.range (i + 1), indexWeight p j) ≤ z i) :
    expectation p hp (fun a ↦ if z a.val < 1 / 2 then 1 / Real.sqrt (z a.val) else 0) ≤
      2 * Real.sqrt (expectation p hp (fun a ↦ if z a.val < 1 / 2 then 1 else 0)) := by
  rw [expectation_eq_sum_range p hp (fun i ↦ if z i < 1 / 2 then 1 / Real.sqrt (z i) else 0),
    expectation_eq_sum_range p hp (fun i ↦ if z i < 1 / 2 then 1 else 0)]
  have h := sum_lower_half_div_sqrt_le (indexWeight p) z n
    (fun i _ ↦ indexWeight_nonneg p i) hz
  have he (i : ℕ) : indexWeight p i * (if z i < 1 / 2 then 1 / Real.sqrt (z i) else 0) =
      if z i < 1 / 2 then indexWeight p i / Real.sqrt (z i) else 0 := by
    split_ifs <;> ring
  have hq (i : ℕ) : indexWeight p i * (if z i < 1 / 2 then 1 else 0) =
      if z i < 1 / 2 then indexWeight p i else 0 := by
    split_ifs <;> ring
  simp_rw [he, hq]
  exact h

lemma expectation_sqrt_odds_le_of_index_cumulative {n : ℕ} (p : PMF (Fin n))
    (hp : p.support.Finite) (z : ℕ → ℝ)
    (hbound : ∀ i < n, z i ∈ Set.Icc 0 1)
    (hz : ∀ i < n, (∑ j ∈ Finset.range (i + 1), indexWeight p j) ≤ z i) :
    expectation p hp (fun a ↦ Real.sqrt ((1 - z a.val) / z a.val)) ≤
      3 * Real.sqrt (2 * expectation p hp (fun a ↦ 1 - z a.val)) := by
  apply expectation_sqrt_odds_le_of_lower_tail p hp (fun a ↦ z a.val)
    (fun a _ ↦ hbound a.val a.isLt)
  exact expectation_lower_half_inv_sqrt_le p hp z hz

end ExactOverlaps.FiniteProbability
