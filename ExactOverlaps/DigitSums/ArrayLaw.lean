/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.DigitSums.BlockEntropy
public import ExactOverlaps.SelfSimilar.EntropySupport

/-!
# Finite arrays of digit values

The multiplicity bound applies to the actual law of an array sum, with the
copies indexed by `Fin m`. The array law can have arbitrary dependence.
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal Classical

namespace ExactOverlaps.DigitSums

open SelfSimilar Entropy

variable {α ι : Type*}

/-- Convert an indexed list of letters to the recursive word representation. -/
def wordOfFn : (m : ℕ) → (Fin m → α) → Word α m
  | 0, _ => PUnit.unit
  | m + 1, f => (f 0, wordOfFn m (fun i ↦ f i.succ))

lemma wordSum_wordOfFn (v : α → ℝ) (m : ℕ) (f : Fin m → α) :
    wordSum v m (wordOfFn m f) = ∑ i, v (f i) := by
  induction m with
  | zero => simp [wordSum]
  | succ m ih => simp [wordOfFn, wordSum, Fin.sum_univ_succ, ih]

/-- A sum of m copies, each with the same coefficients and digit value lists. -/
def arraySum [Fintype ι] (v : ι → α → ℝ) (a : ι → ℝ) (m : ℕ)
    (x : Fin m → ι → α) : ℝ := ∑ i, ∑ j, a j * v j (x i j)

lemma arraySum_eq_blockSum [Fintype ι] (v : ι → α → ℝ) (a : ι → ℝ) (m : ℕ)
    (x : Fin m → ι → α) :
    arraySum v a m x = blockSum v a m (fun j ↦ wordOfFn m (fun i ↦ x i j)) := by
  simp only [arraySum, blockSum, wordSum_wordOfFn, Finset.mul_sum]
  exact Finset.sum_comm

lemma arraySumLaw_eq [Fintype ι] (v : ι → α → ℝ) (a : ι → ℝ) (m : ℕ)
    (p : PMF (Fin m → ι → α)) :
    p.map (arraySum v a m) = blockSumLaw v a m
      (p.map (fun x j ↦ wordOfFn m (fun i ↦ x i j))) := by
  rw [blockSumLaw, PMF.map_comp]
  congr 1
  funext x
  exact arraySum_eq_blockSum v a m x

lemma arraySumLaw_support_finite [Fintype α] [Fintype ι]
    (v : ι → α → ℝ) (a : ι → ℝ) (m : ℕ)
    (p : PMF (Fin m → ι → α)) : (p.map (arraySum v a m)).support.Finite := by
  rw [PMF.support_map]
  exact (Set.toFinite _).image _

/-- The sharp digit-count entropy bound for an actual array law. -/
theorem arraySumLaw_entropy_le [Fintype α] [DecidableEq α] [Fintype ι]
    (v : ι → α → ℝ) (a : ι → ℝ) (a₀ : α) (m : ℕ)
    (p : PMF (Fin m → ι → α)) :
    finiteEntropy (p.map (arraySum v a m)) (arraySumLaw_support_finite v a m p) ≤
      (Fintype.card ι : ℝ) * (Fintype.card α - 1 : ℕ) * Real.log (m + 1 : ℝ) := by
  have h := blockSumLaw_entropy_le v a a₀ m
    (p.map (fun x j ↦ wordOfFn m (fun i ↦ x i j)))
  simpa only [← arraySumLaw_eq] using h

end ExactOverlaps.DigitSums
