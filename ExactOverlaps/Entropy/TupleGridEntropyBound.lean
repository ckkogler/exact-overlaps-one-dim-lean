module

public import ExactOverlaps.Entropy.OrderedCutEntropy
public import ExactOverlaps.Entropy.TupleCutEntropy

/-!
# The finite grid-cut bound inside an independent tuple cell

For each selected coordinate, integrating its cut entropy controls the
length-weighted sum over all common-grid gaps. Summing over coordinates
gives exactly nine times the number of inputs times the sum of their
dispersions. The laws may be arbitrary normalized coordinate cell laws.
-/

@[expose] public section

open scoped BigOperators Classical
open ExactOverlaps.FiniteLaw

namespace ExactOverlaps.Entropy

theorem sum_grid_tuple_cut_entropy_le {m n : ℕ} (p : Fin m → PMF (Fin (n + 1)))
    (hp : ∀ i, (p i).support.Finite) (x : ℕ → ℝ)
    (hx : Monotone (fun k : Fin (n + 1) ↦ x k.val)) (i : Fin m) :
    (∑ j : Fin n, (x (j.val + 1) - x j.val) *
      averageStatisticConditionalEntropy (tupleLaw m p) (tupleLaw_support_finite m p hp)
        (tupleSum (fun k ↦ x k.val) m)
        (fun w ↦ decide (j.val < (tupleCoordinate m w i).val))) ≤
      9 * ∑ k, dispersion (p k) (hp k) (fun a ↦ x a.val) := by
  have hi := integrable_conditional_tuple_cut_entropy (fun k : Fin (n + 1) ↦ x k.val) m p hp i
  have h₁ := sum_grid_cut_entropy_le_integral (tupleLaw m p) (tupleLaw_support_finite m p hp)
    (tupleSum (fun k : Fin (n + 1) ↦ x k.val) m) (fun w ↦ tupleCoordinate m w i) x hx hi
  have h₂ := integral_conditional_tuple_cut_entropy_le (fun k : Fin (n + 1) ↦ x k.val) m p hp i
  exact h₁.trans h₂

theorem sum_all_grid_tuple_cut_entropy_le {m n : ℕ} (p : Fin m → PMF (Fin (n + 1)))
    (hp : ∀ i, (p i).support.Finite) (x : ℕ → ℝ)
    (hx : Monotone (fun k : Fin (n + 1) ↦ x k.val)) :
    (∑ i : Fin m, ∑ j : Fin n, (x (j.val + 1) - x j.val) *
      averageStatisticConditionalEntropy (tupleLaw m p) (tupleLaw_support_finite m p hp)
        (tupleSum (fun k ↦ x k.val) m)
        (fun w ↦ decide (j.val < (tupleCoordinate m w i).val))) ≤
      9 * m * ∑ k, dispersion (p k) (hp k) (fun a ↦ x a.val) := by
  apply (Finset.sum_le_sum (fun i _ ↦ sum_grid_tuple_cut_entropy_le p hp x hx i)).trans_eq
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end ExactOverlaps.Entropy
