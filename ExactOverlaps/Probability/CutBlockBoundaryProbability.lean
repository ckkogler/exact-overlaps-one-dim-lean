module

public import ExactOverlaps.Probability.CutBlockProbability
public import ExactOverlaps.Probability.PoissonBoundaryKernels

/-!
# Interior and boundary probabilities of contiguous cut cells

The neighboring-gap product has two, one, or zero factors according to
which endpoints of the full support are contained in the block.
-/

@[expose] public section

open scoped BigOperators Classical

namespace ExactOverlaps.Poisson

lemma neighboringGaps_interior {n : ℕ} (i j : Fin n) :
    neighboringGaps i.succ j.castSucc = {i, j} := by
  ext k
  simp only [neighboringGaps, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (hi | hj)
    · exact Or.inl (Fin.ext (by simpa using Nat.add_right_cancel hi))
    · exact Or.inr (Fin.ext hj)
  · rintro (rfl | rfl) <;> simp

lemma neighboringGaps_left {n : ℕ} (j : Fin n) :
    neighboringGaps 0 j.castSucc = {j} := by
  ext k
  simp only [neighboringGaps, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · rintro (hi | hj)
    · have : k.val + 1 = 0 := hi
      omega
    · exact Fin.ext hj
  · rintro rfl
    exact Or.inr rfl

lemma neighboringGaps_right {n : ℕ} (i : Fin n) :
    neighboringGaps i.succ (Fin.last n) = {i} := by
  ext k
  simp only [neighboringGaps, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · rintro (hi | hj)
    · exact Fin.ext (by simpa using Nat.add_right_cancel hi)
    · have : k.val = n := hj
      have := k.isLt
      omega
  · rintro rfl
    exact Or.inl rfl

lemma neighboringGaps_full (n : ℕ) :
    neighboringGaps (0 : Fin (n + 1)) (Fin.last n) = ∅ := by
  ext k
  simp only [neighboringGaps, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.notMem_empty, iff_false]
  intro h
  have hk := k.isLt
  change k.val + 1 = 0 ∨ k.val = n at h
  omega

lemma ordered_blockWeight_interior {n : ℕ} (x : ℕ → ℝ) (t : ℝ)
    (i j : Fin n) (hij : i.succ ≤ j.castSucc) :
    blockWeight (orderedGapLength x n) t i.succ j.castSucc =
      cellSurvival (x j.val - x (i.val + 1))
        (x (i.val + 1) - x i.val) (x (j.val + 1) - x j.val) t := by
  have hne : i ≠ j := by
    intro h
    have hv : i.val + 1 ≤ j.val := hij
    subst j
    omega
  rw [ordered_blockWeight_eq x t _ _ hij, neighboringGaps_interior]
  rw [Finset.prod_insert (show i ∉ ({j} : Finset (Fin n)) by simpa using hne),
    Finset.prod_singleton]
  simp only [cellSurvival, orderedGapLength, Fin.val_succ, Fin.val_castSucc]
  ring

lemma ordered_blockWeight_left {n : ℕ} (x : ℕ → ℝ) (t : ℝ) (j : Fin n) :
    blockWeight (orderedGapLength x n) t 0 j.castSucc =
      boundarySurvival (x j.val - x 0) (x (j.val + 1) - x j.val) t := by
  rw [ordered_blockWeight_eq x t _ _ (Fin.zero_le _), neighboringGaps_left]
  simp [boundarySurvival, orderedGapLength]

lemma ordered_blockWeight_right {n : ℕ} (x : ℕ → ℝ) (t : ℝ) (i : Fin n) :
    blockWeight (orderedGapLength x n) t i.succ (Fin.last n) =
      boundarySurvival (x n - x (i.val + 1)) (x (i.val + 1) - x i.val) t := by
  rw [ordered_blockWeight_eq x t _ _ (Fin.le_last _), neighboringGaps_right]
  simp [boundarySurvival, orderedGapLength]

lemma ordered_blockWeight_full (n : ℕ) (x : ℕ → ℝ) (t : ℝ) :
    blockWeight (orderedGapLength x n) t 0 (Fin.last n) =
      Real.exp (-((x n - x 0) * t)) := by
  rw [ordered_blockWeight_eq x t _ _ (Fin.zero_le _), neighboringGaps_full]
  simp

end ExactOverlaps.Poisson
