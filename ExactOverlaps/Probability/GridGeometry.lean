module

public import ExactOverlaps.Probability.ProductCutCells

/-!
# Separation by the sides of a finite ordered grid

Every two different grid indices are distinguished by one gap. Coordinate
gap observations therefore determine the complete finite tuple.
-/

@[expose] public section

open Set
open scoped Classical
open ExactOverlaps.Entropy

namespace ExactOverlaps.Poisson

lemma grid_monotoneOn {n : ℕ} (x : ℕ → ℝ)
    (hx : Monotone (fun k : Fin (n + 1) ↦ x k.val)) : MonotoneOn x (Icc 0 n) := by
  intro a ha b hb hab
  exact hx (show (⟨a, Nat.lt_succ_iff.mpr ha.2⟩ : Fin (n + 1)) ≤
    ⟨b, Nat.lt_succ_iff.mpr hb.2⟩ from hab)

lemma grid_gap_pos {n : ℕ} (x : ℕ → ℝ)
    (hx : StrictMono (fun k : Fin (n + 1) ↦ x k.val)) (j : Fin n) :
    0 < orderedGapLength x n j := by
  apply sub_pos.mpr
  exact hx (show (⟨j.val, by omega⟩ : Fin (n + 1)) < ⟨j.val + 1, by omega⟩ from Nat.lt_succ_self j.val)

lemma indexSide_separates (n : ℕ) : Function.Injective (fun a : Fin (n + 1) ↦
    fun j : Fin n ↦ indexSide n j a) := by
  intro a b hab
  apply Fin.ext
  by_contra h
  rcases lt_or_gt_of_ne h with hlt | hgt
  · let j : Fin n := ⟨a.val, by omega⟩
    have hj := congrArg (fun f ↦ f j) hab
    simp [indexSide, j, hlt] at hj
  · let j : Fin n := ⟨b.val, by omega⟩
    have hj := congrArg (fun f ↦ f j) hab
    simp [indexSide, j, hgt] at hj

lemma tupleGridSide_separates (m n : ℕ) : Function.Injective
    (fun a : FiniteTuple (Fin (n + 1)) m ↦ fun ij ↦ tupleGridSide m n ij a) := by
  intro a b hab
  apply (tuple_eq_iff_coordinate_eq m a b).mpr
  intro i
  apply indexSide_separates n
  funext j
  exact congrArg (fun f ↦ f (i, j)) hab

end ExactOverlaps.Poisson
