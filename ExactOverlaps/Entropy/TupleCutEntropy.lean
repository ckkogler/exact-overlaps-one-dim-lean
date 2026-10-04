module

public import ExactOverlaps.Entropy.CumulativeEntropyBound
public import ExactOverlaps.Entropy.ConditionalEntropyMap
public import ExactOverlaps.Probability.FiniteProductDispersion

/-!
# One-coordinate cumulative entropy in a finite independent tuple

The selected coordinate and the sum of the remaining coordinates have the
actual independent joint law. The two-variable cumulative entropy estimate
and the dispersion triangle inequality therefore bound each selected input
by nine times the sum of all marginal dispersions.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators Classical
open ExactOverlaps.FiniteLaw

namespace ExactOverlaps.Entropy

lemma conditional_tuple_cut_entropy_eq {α : Type*} (x : α → ℝ) (n : ℕ)
    (p : Fin n → PMF α) (hp : ∀ i, (p i).support.Finite) (i : Fin n) (a : ℝ) :
    conditionalCutEntropy (tupleLaw n p) (tupleLaw_support_finite n p hp)
      (tupleSum x n) (fun w ↦ x (tupleCoordinate n w i)) a =
    conditionalCutEntropy
      (independentPair ((p i).map x) ((tupleLaw n p).map (tupleSumExcept x n i)))
      (independentPair_support_finite _ _ (by simpa using (hp i).image x)
        (by simpa using (tupleLaw_support_finite n p hp).image (tupleSumExcept x n i)))
      (fun z ↦ z.1 + z.2) Prod.fst a := by
  let k : FiniteTuple α n → ℝ × ℝ := fun w ↦ (x (tupleCoordinate n w i), tupleSumExcept x n i w)
  have h := averageStatisticConditionalEntropy_map (tupleLaw n p)
    (tupleLaw_support_finite n p hp) k (fun z ↦ z.1 + z.2) (fun z ↦ decide (z.1 ≤ a))
  have hs : (fun w ↦ (k w).1 + (k w).2) = tupleSum x n := by
    funext w
    dsimp only [k, tupleSumExcept]
    ring
  rw [hs] at h
  apply h.symm.trans
  exact averageStatisticConditionalEntropy_congr (tupleLaw_coordinate_sumExcept x n p i)
    _ _ _ _

theorem integrable_conditional_tuple_cut_entropy {α : Type*} (x : α → ℝ) (n : ℕ)
    (p : Fin n → PMF α) (hp : ∀ i, (p i).support.Finite) (i : Fin n) :
    Integrable (conditionalCutEntropy (tupleLaw n p) (tupleLaw_support_finite n p hp)
      (tupleSum x n) (fun w ↦ x (tupleCoordinate n w i))) := by
  have he := funext (conditional_tuple_cut_entropy_eq x n p hp i)
  rw [he]
  exact integrable_conditional_sum_cut_entropy ((p i).map x)
    ((tupleLaw n p).map (tupleSumExcept x n i))
    (by simpa using (hp i).image x)
    (by simpa using (tupleLaw_support_finite n p hp).image (tupleSumExcept x n i)) id id

theorem integral_conditional_tuple_cut_entropy_le {α : Type*} (x : α → ℝ) (n : ℕ)
    (p : Fin n → PMF α) (hp : ∀ i, (p i).support.Finite) (i : Fin n) :
    (∫ a, conditionalCutEntropy (tupleLaw n p) (tupleLaw_support_finite n p hp)
      (tupleSum x n) (fun w ↦ x (tupleCoordinate n w i)) a) ≤
      9 * ∑ j, dispersion (p j) (hp j) x := by
  have h := integral_conditional_sum_cut_entropy_le ((p i).map x)
    ((tupleLaw n p).map (tupleSumExcept x n i))
    (by simpa using (hp i).image x)
    (by simpa using (tupleLaw_support_finite n p hp).image (tupleSumExcept x n i)) id id
  have he := funext (conditional_tuple_cut_entropy_eq x n p hp i)
  rw [he]
  apply h.trans
  rw [dispersion_map (p i) (hp i) x id,
    dispersion_map (tupleLaw n p) (tupleLaw_support_finite n p hp) (tupleSumExcept x n i) id]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have hd := dispersion_tupleSumExcept_le x n p hp i
  have hs := Finset.add_sum_erase Finset.univ (fun j ↦ dispersion (p j) (hp j) x) (Finset.mem_univ i)
  change dispersion (p i) (hp i) x +
    dispersion (tupleLaw n p) (tupleLaw_support_finite n p hp) (tupleSumExcept x n i) ≤ _
  linarith

end ExactOverlaps.Entropy
