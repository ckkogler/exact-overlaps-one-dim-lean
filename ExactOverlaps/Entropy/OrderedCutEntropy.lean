module

public import ExactOverlaps.Entropy.CutEntropy
public import ExactOverlaps.Entropy.DeterministicConditional
public import ExactOverlaps.Probability.OrderedIntervals

/-!
# Length-weighted grid-cut entropy and the actual cut integral

On each half-open grid gap, the real threshold event is the complement of
the corresponding index-side label. Complementary binary labels have equal
conditional entropy. Integrating over disjoint gaps therefore bounds their
length-weighted entropy sum by the full cumulative conditional entropy.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators Classical

namespace ExactOverlaps.Entropy

lemma grid_threshold_iff_index_le {n : ℕ} (x : ℕ → ℝ)
    (hx : Monotone (fun k : Fin (n + 1) ↦ x k.val))
    (j : Fin n) (k : Fin (n + 1)) {a : ℝ} (ha : a ∈ Ico (x j.val) (x (j.val + 1))) :
    x k.val ≤ a ↔ k.val ≤ j.val := by
  constructor
  · intro hka
    by_contra hkj
    have hjk : j.succ ≤ k := by exact_mod_cast Nat.succ_le_of_lt (Nat.lt_of_not_ge hkj)
    have hm := hx hjk
    exact (not_lt_of_ge (hm.trans hka)) ha.2
  · intro hkj
    exact (hx (show k ≤ j.castSucc from hkj)).trans ha.1

lemma conditionalCutEntropy_on_grid_gap {α β : Type*} {n : ℕ} (p : PMF α)
    (hp : p.support.Finite) (s : α → β) (index : α → Fin (n + 1)) (x : ℕ → ℝ)
    (hx : Monotone (fun k : Fin (n + 1) ↦ x k.val)) (j : Fin n)
    {a : ℝ} (ha : a ∈ Ico (x j.val) (x (j.val + 1))) :
    conditionalCutEntropy p hp s (fun z ↦ x (index z).val) a =
      averageStatisticConditionalEntropy p hp s (fun z ↦ decide (j.val < (index z).val)) := by
  have he : (fun z ↦ decide (x (index z).val ≤ a)) =
      (fun z ↦ !decide (j.val < (index z).val)) := by
    funext z
    simp only [grid_threshold_iff_index_le x hx j (index z) ha, ← decide_not, Nat.not_lt]
  unfold conditionalCutEntropy
  rw [he, averageStatisticConditionalEntropy_bool_not]

theorem sum_grid_cut_entropy_le_integral {α β : Type*} {n : ℕ} (p : PMF α)
    (hp : p.support.Finite) (s : α → β) (index : α → Fin (n + 1)) (x : ℕ → ℝ)
    (hx : Monotone (fun k : Fin (n + 1) ↦ x k.val))
    (hi : Integrable (conditionalCutEntropy p hp s (fun z ↦ x (index z).val))) :
    (∑ j : Fin n, (x (j.val + 1) - x j.val) *
      averageStatisticConditionalEntropy p hp s (fun z ↦ decide (j.val < (index z).val))) ≤
      ∫ a, conditionalCutEntropy p hp s (fun z ↦ x (index z).val) a := by
  exact FiniteProbability.sum_gap_mul_le_integral x hx _ _ hi
    (conditionalCutEntropy_nonneg p hp s _)
    (fun j _ ha ↦ conditionalCutEntropy_on_grid_gap p hp s index x hx j ha)

end ExactOverlaps.Entropy
