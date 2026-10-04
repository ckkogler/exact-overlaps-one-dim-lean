module

public import ExactOverlaps.Probability.IndexedQuantile
public import ExactOverlaps.Probability.FiniteDistanceTail

/-!
# Shifted cumulative-distribution estimate on ordered finite laws

Every initial segment lies below the shifted observed atom. Its mass is a
lower bound for the shifted cumulative mass, so the finite quantile estimate
gives the square-root odds bound with the actual independent-sample tail.
-/

@[expose] public section

open scoped BigOperators Classical

namespace ExactOverlaps.FiniteProbability

lemma index_cumulative_le_shiftedCDF {n : ℕ} (p : PMF (Fin n))
    (hp : p.support.Finite) (x : ℕ → ℝ)
    (hx : Monotone (fun a : Fin n ↦ x a.val)) {r : ℝ} (hr : 0 ≤ r)
    (i : ℕ) (hi : i < n) :
    (∑ j ∈ Finset.range (i + 1), indexWeight p j) ≤
      cumulativeMass p hp (fun a ↦ x a.val) (x i + r) := by
  rw [cumulativeMass, expectation_eq_sum_range p hp (fun j ↦ if x j ≤ x i + r then 1 else 0)]
  calc
    (∑ j ∈ Finset.range (i + 1), indexWeight p j) =
        ∑ j ∈ Finset.range (i + 1), indexWeight p j * (if x j ≤ x i + r then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hji : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hjn : j < n := hji.trans_lt hi
      have hm := hx (show (⟨j, hjn⟩ : Fin n) ≤ ⟨i, hi⟩ from hji)
      have hbound : x j ≤ x i + r := hm.trans (le_add_of_nonneg_right hr)
      simp [hbound]
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_of_lt hi))
      intro j _ _
      apply mul_nonneg (indexWeight_nonneg p j)
      split_ifs <;> norm_num

theorem expectation_shiftedCDF_sqrt_odds_le {n : ℕ} (p : PMF (Fin n))
    (hp : p.support.Finite) (x : ℕ → ℝ)
    (hx : Monotone (fun a : Fin n ↦ x a.val)) {r : ℝ} (hr : 0 ≤ r) :
    expectation p hp (fun a ↦ Real.sqrt
      ((1 - cumulativeMass p hp (fun z ↦ x z.val) (x a.val + r)) /
        cumulativeMass p hp (fun z ↦ x z.val) (x a.val + r))) ≤
      3 * Real.sqrt (2 * distanceTail p hp (fun a ↦ x a.val) r) := by
  rw [distanceTail_eq_cumulative_complement]
  apply expectation_sqrt_odds_le_of_index_cumulative p hp
    (fun i ↦ cumulativeMass p hp (fun z ↦ x z.val) (x i + r))
  · intro i _
    exact ⟨cumulativeMass_nonneg p hp _ _, cumulativeMass_le_one p hp _ _⟩
  · exact index_cumulative_le_shiftedCDF p hp x hx hr

end ExactOverlaps.FiniteProbability
