module

public import ExactOverlaps.SelfSimilar.RatioCounts
public import ExactOverlaps.SelfSimilar.EntropyComparison

/-!
A common finite alphabet for blocks of every length at most `N`. Its signed
ratios still have only polynomially many possibilities, because the same
letter-count vector reconstructs the ratio regardless of the block length.
-/

@[expose] public section

open scoped BigOperators Classical

namespace ExactOverlaps.SelfSimilar

def BoundedWord (ι : Type*) (N : ℕ) := Σ j : Fin (N + 1), Word ι j.val

instance {ι : Type*} [Fintype ι] (N : ℕ) : Fintype (BoundedWord ι N) :=
  inferInstanceAs (Fintype (Σ j : Fin (N + 1), Word ι j.val))

def BoundedWord.empty {ι : Type*} (N : ℕ) : BoundedWord ι N :=
  ⟨⟨0, Nat.zero_lt_succ N⟩, PUnit.unit⟩

noncomputable def BoundedWord.countVector {ι : Type*} [DecidableEq ι]
    (N : ℕ) (w : BoundedWord ι N) : ι → Fin (N + 1) :=
  fun a ↦ ⟨wordCount w.1.val w.2 a,
    Nat.lt_succ_of_le ((wordCount_le w.1.val w.2 a).trans (Nat.le_of_lt_succ w.1.isLt))⟩

namespace System

variable {ι : Type*} [Fintype ι]

noncomputable def boundedWordMap (S : System ι) (N : ℕ) (w : BoundedWord ι N) : RealSimilarity :=
  S.wordMap w.1.val w.2

noncomputable def boundedWordRatio (S : System ι) (N : ℕ) (w : BoundedWord ι N) : ℝ :=
  (S.boundedWordMap N w).ratio

noncomputable def boundedWordTranslation (S : System ι) (N : ℕ) (w : BoundedWord ι N) : ℝ :=
  (S.boundedWordMap N w).shift

theorem boundedWordRatio_eq_counts (S : System ι) (N : ℕ) (w : BoundedWord ι N) :
    S.boundedWordRatio N w = S.ratioFromCounts N (w.countVector N) := by
  exact S.wordRatio_eq_prod_count w.1.val w.2

theorem card_boundedWordRatios_le (S : System ι) (N : ℕ) :
    (Finset.univ.image (S.boundedWordRatio N)).card ≤ (N + 1) ^ Fintype.card ι := by
  have hsub : Finset.univ.image (S.boundedWordRatio N) ⊆
      Finset.univ.image (S.ratioFromCounts N) := by
    intro t ht
    obtain ⟨w, _, hw⟩ := Finset.mem_image.mp ht
    exact Finset.mem_image.mpr
      ⟨w.countVector N, Finset.mem_univ _, (S.boundedWordRatio_eq_counts N w).symm.trans hw⟩
  calc
    _ ≤ (Finset.univ.image (S.ratioFromCounts N)).card := Finset.card_le_card hsub
    _ ≤ Fintype.card (ι → Fin (N + 1)) := Finset.card_image_le
    _ = (N + 1) ^ Fintype.card ι := by simp

theorem boundedWordRatio_entropy_le (S : System ι) (N : ℕ) (p : PMF (BoundedWord ι N)) :
    Entropy.finiteEntropy (p.map (S.boundedWordRatio N))
      (by simpa using (Set.toFinite p.support).image (S.boundedWordRatio N)) ≤
      (Fintype.card ι : ℝ) * Real.log (N + 1 : ℝ) := by
  have hc : (show (p.map (S.boundedWordRatio N)).support.Finite from by
      simpa using (Set.toFinite p.support).image (S.boundedWordRatio N)).toFinset.card ≤
      (N + 1) ^ Fintype.card ι := by
    apply le_trans (Finset.card_le_card (t := Finset.univ.image (S.boundedWordRatio N)) ?_)
      (S.card_boundedWordRatios_le N)
    intro t ht
    obtain ⟨w, _, hw⟩ := (PMF.mem_support_map_iff _ p t).mp (by simpa using ht)
    exact Finset.mem_image.mpr ⟨w, Finset.mem_univ _, hw⟩
  have h := Entropy.finiteEntropy_le_log_of_card_le _ _ hc
  simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one, Real.log_pow] using h

end System
end ExactOverlaps.SelfSimilar
