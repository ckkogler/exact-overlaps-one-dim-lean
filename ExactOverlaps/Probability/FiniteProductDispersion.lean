module

public import ExactOverlaps.Entropy.IndependentCoordinate
public import ExactOverlaps.Probability.DispersionMap

/-!
# Dispersion of the sum excluding one independent input

The total sum minus one coordinate is exactly the sum over the remaining
finite indices. The absolute-distance triangle inequality bounds its
dispersion by the sum of the genuine marginal dispersions.
-/

@[expose] public section

open scoped BigOperators Classical
open ExactOverlaps.Entropy

namespace ExactOverlaps.FiniteLaw

lemma tupleSum_eq_sum_coordinates {α : Type*} (x : α → ℝ) (n : ℕ)
    (w : FiniteTuple α n) : tupleSum x n w = ∑ i, x (tupleCoordinate n w i) := by
  induction n with
  | zero => simp [tupleSum]
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    change x w.1 + tupleSum x n w.2 = x w.1 + ∑ i, x (tupleCoordinate n w.2 i)
    rw [ih]

lemma tupleSumExcept_eq_sum_erase {α : Type*} (x : α → ℝ) (n : ℕ)
    (i : Fin n) (w : FiniteTuple α n) :
    tupleSumExcept x n i w = ∑ j ∈ Finset.univ.erase i, x (tupleCoordinate n w j) := by
  unfold tupleSumExcept
  rw [tupleSum_eq_sum_coordinates]
  have h := Finset.sum_erase_add Finset.univ (fun j ↦ x (tupleCoordinate n w j)) (Finset.mem_univ i)
  linarith

lemma dispersion_tupleCoordinate {α : Type*} (x : α → ℝ) (n : ℕ)
    (p : Fin n → PMF α) (hp : ∀ i, (p i).support.Finite) (i : Fin n) :
    dispersion (tupleLaw n p) (tupleLaw_support_finite n p hp)
      (fun w ↦ x (tupleCoordinate n w i)) = dispersion (p i) (hp i) x := by
  rw [← dispersion_map (tupleLaw n p) (tupleLaw_support_finite n p hp)
    (fun w ↦ tupleCoordinate n w i) x]
  congr 1
  exact tupleLaw_coordinate n p i

theorem dispersion_tupleSumExcept_le {α : Type*} (x : α → ℝ) (n : ℕ)
    (p : Fin n → PMF α) (hp : ∀ i, (p i).support.Finite) (i : Fin n) :
    dispersion (tupleLaw n p) (tupleLaw_support_finite n p hp) (tupleSumExcept x n i) ≤
      ∑ j ∈ Finset.univ.erase i, dispersion (p j) (hp j) x := by
  have he : tupleSumExcept x n i =
      (fun w ↦ ∑ j ∈ Finset.univ.erase i, x (tupleCoordinate n w j)) := by
    funext w
    exact tupleSumExcept_eq_sum_erase x n i w
  rw [he]
  apply (dispersion_sum_le (tupleLaw n p) (tupleLaw_support_finite n p hp)
    (Finset.univ.erase i) (fun j w ↦ x (tupleCoordinate n w j))).trans_eq
  apply Finset.sum_congr rfl
  intro j _
  exact dispersion_tupleCoordinate x n p hp j

end ExactOverlaps.FiniteLaw
