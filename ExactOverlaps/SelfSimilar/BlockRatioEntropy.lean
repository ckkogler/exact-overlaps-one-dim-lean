module

public import ExactOverlaps.SelfSimilar.BoundedWords
public import ExactOverlaps.Entropy.IndependentPair

/-! The vector of signed ratios of bounded blocks has small entropy. -/

@[expose] public section

open scoped BigOperators Classical

namespace ExactOverlaps.SelfSimilar.System

open Entropy
variable {ι : Type*} [Fintype ι]

theorem blockRatioVector_entropy_le (S : System ι) (N L : ℕ)
    (p : PMF (Fin L → BoundedWord ι N)) :
    finiteEntropy (p.map (fun x j ↦ S.boundedWordRatio N (x j)))
      (by simpa using (Set.toFinite p.support).image (fun x j ↦ S.boundedWordRatio N (x j))) ≤
      (L : ℝ) * Fintype.card ι * Real.log (N + 1 : ℝ) := by
  let f : (Fin L → BoundedWord ι N) → Fin L → (ι → Fin (N + 1)) :=
    fun x j ↦ (x j).countVector N
  let g : (Fin L → (ι → Fin (N + 1))) → Fin L → ℝ :=
    fun c j ↦ S.ratioFromCounts N (c j)
  have he : (p.map f).map g = p.map (fun x j ↦ S.boundedWordRatio N (x j)) := by
    rw [PMF.map_comp]
    congr 1
    funext x j
    exact (S.boundedWordRatio_eq_counts N (x j)).symm
  have hf : (p.map f).support.Finite := Set.toFinite _
  have hmap := finiteEntropy_map_le (p.map f) hf g
  simp only [he] at hmap
  have hcard := finiteEntropy_le_log_of_card_le (p.map f) hf
    (show hf.toFinset.card ≤ Fintype.card (Fin L → (ι → Fin (N + 1))) from Finset.card_le_univ _)
  have hlog : Real.log (Fintype.card (Fin L → (ι → Fin (N + 1)))) =
      (L : ℝ) * Fintype.card ι * Real.log (N + 1 : ℝ) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_add,
      Nat.cast_one, Real.log_pow]
    ring
  exact hmap.trans (hcard.trans_eq hlog)

end ExactOverlaps.SelfSimilar.System
