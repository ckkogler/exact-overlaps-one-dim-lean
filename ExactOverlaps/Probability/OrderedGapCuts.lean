module

public import ExactOverlaps.Probability.CutObservations
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Fin
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# Gap cuts on a finite ordered real support

For atoms indexed by `Fin (n+1)`, a cut in gap `i` separates the indices at
most `i` from the larger indices. The total length of the separating gaps
is the distance between the atoms, giving the exact exponential same-cell
probability used in the variance-energy estimate.
-/

@[expose] public section

open scoped BigOperators ENNReal Classical

namespace ExactOverlaps.Poisson

def indexSide (n : ℕ) (i : Fin n) (a : Fin (n + 1)) : Bool := decide (i.val < a.val)

noncomputable def orderedGapLength (x : ℕ → ℝ) (n : ℕ) (i : Fin n) : ℝ :=
  x (i.val + 1) - x i.val

lemma orderedGapLength_nonneg (x : ℕ → ℝ) (n : ℕ)
    (hx : MonotoneOn x (Set.Icc 0 n)) (i : Fin n) : 0 ≤ orderedGapLength x n i := by
  exact sub_nonneg.mpr (hx ⟨Nat.zero_le _, (Nat.le_of_lt i.isLt)⟩
    ⟨Nat.zero_le _, Nat.succ_le_of_lt i.isLt⟩ (Nat.le_succ _))

lemma sum_orderedGapLength_of_le (x : ℕ → ℝ) (n : ℕ) (a b : Fin (n + 1))
    (hab : a.val ≤ b.val) :
    (∑ i ∈ separatingCuts (indexSide n) a b, orderedGapLength x n i) =
      x b.val - x a.val := by
  have hs : separatingCuts (indexSide n) a b =
      Finset.univ.filter (fun i : Fin n ↦ a.val ≤ i.val ∧ i.val < b.val) := by
    ext i
    simp only [separatingCuts, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hia : i.val < a.val <;> by_cases hib : i.val < b.val <;>
      simp [indexSide, hia, hib] <;> omega
  rw [hs, Finset.sum_filter]
  change (∑ i : Fin n, if a.val ≤ i.val ∧ i.val < b.val
    then x (i.val + 1) - x i.val else 0) = _
  rw [Fin.sum_univ_eq_sum_range (fun i ↦
    if a.val ≤ i ∧ i < b.val then x (i + 1) - x i else 0)]
  rw [← Finset.sum_filter]
  have hr : (Finset.range n).filter (fun i ↦ a.val ≤ i ∧ i < b.val) =
      Finset.Ico a.val b.val := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    have hb := b.isLt
    omega
  rw [hr, Finset.sum_Ico_eq_sub _ hab, Finset.sum_range_sub, Finset.sum_range_sub]
  ring

lemma sum_orderedGapLength (x : ℕ → ℝ) (n : ℕ)
    (hx : MonotoneOn x (Set.Icc 0 n)) (a b : Fin (n + 1)) :
    (∑ i ∈ separatingCuts (indexSide n) a b, orderedGapLength x n i) =
      |x a.val - x b.val| := by
  have ha : a.val ∈ Set.Icc 0 n := ⟨Nat.zero_le _, Nat.lt_succ_iff.mp a.isLt⟩
  have hb : b.val ∈ Set.Icc 0 n := ⟨Nat.zero_le _, Nat.lt_succ_iff.mp b.isLt⟩
  rcases le_total a.val b.val with hab | hba
  · rw [sum_orderedGapLength_of_le x n a b hab, abs_of_nonpos (sub_nonpos.mpr (hx ha hb hab))]
    ring
  · have hs : separatingCuts (indexSide n) a b = separatingCuts (indexSide n) b a := by
      ext i
      simp [separatingCuts, ne_comm]
    rw [hs, sum_orderedGapLength_of_le x n b a hba,
      abs_of_nonneg (sub_nonneg.mpr (hx hb ha hba))]

/-- The finite ordered-support cut model has exactly the Poisson same-cell probability. -/
lemma orderedCutPMF_same_label (x : ℕ → ℝ) (n : ℕ)
    (hx : MonotoneOn x (Set.Icc 0 n)) (t : ℝ) (ht : 0 ≤ t) (a b : Fin (n + 1)) :
    (∑ c : Fin n → Bool, if cutLabel (indexSide n) c a = cutLabel (indexSide n) c b
      then (cutPMF (orderedGapLength x n) (orderedGapLength_nonneg x n hx) t ht c).toReal
      else 0) = Real.exp (-(|x a.val - x b.val| * t)) := by
  have h := cutPMF_same_label (orderedGapLength x n) (orderedGapLength_nonneg x n hx)
    t ht (indexSide n) a b
  rw [sum_orderedGapLength x n hx a b] at h
  refine Eq.trans ?_ h
  apply Finset.sum_congr (by ext c; simp)
  intro c _
  split_ifs <;> rfl

end ExactOverlaps.Poisson
