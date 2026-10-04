module

public import ExactOverlaps.SelfSimilar.Words

/-!
The signed multiplier of a word depends only on its letter counts. This gives
a polynomial bound on the number of contraction classes, with no arithmetic
or sign restriction on the individual multipliers.
-/

@[expose] public section

open scoped BigOperators

namespace ExactOverlaps.SelfSimilar

variable {ι : Type*} [DecidableEq ι]

/-- The multiplicity of a letter in a finite word. -/
def wordCount : (n : ℕ) → Word ι n → ι → ℕ
  | 0, _, _ => 0
  | n + 1, w, i => (if w.1 = i then 1 else 0) + wordCount n w.2 i

theorem wordCount_le (n : ℕ) (w : Word ι n) (i : ι) : wordCount n w i ≤ n := by
  induction n with
  | zero => simp [wordCount]
  | succ n ih =>
    have h := ih w.2
    simp only [wordCount]
    split_ifs <;> omega

/-- Count vectors take values in a finite cube of side length `n+1`. -/
def wordCountVector (n : ℕ) (w : Word ι n) : ι → Fin (n + 1) :=
  fun i ↦ ⟨wordCount n w i, Nat.lt_succ_of_le (wordCount_le n w i)⟩

namespace System

variable [Fintype ι]

theorem wordRatio_eq_prod_count (S : System ι) (n : ℕ) (w : Word ι n) :
    S.wordRatio n w = ∏ i, (S.map i).ratio ^ wordCount n w i := by
  induction n with
  | zero => simp [wordRatio, wordMap, RealSimilarity.identity, wordCount]
  | succ n ih =>
    rw [S.wordRatio_succ, ih]
    simp only [wordCount, pow_add]
    rw [Finset.prod_mul_distrib]
    congr 1
    simp

/-- Reconstruct the multiplier from its letter-count vector. -/
noncomputable def ratioFromCounts (S : System ι) (n : ℕ)
    (c : ι → Fin (n + 1)) : ℝ := ∏ i, (S.map i).ratio ^ (c i).val

theorem wordRatio_eq_ratioFromCounts (S : System ι) (n : ℕ) (w : Word ι n) :
    S.wordRatio n w = S.ratioFromCounts n (wordCountVector n w) :=
  S.wordRatio_eq_prod_count n w

/-- At most `(n+1)^k` different signed multipliers occur among words of length n. -/
theorem card_wordRatios_le (S : System ι) (n : ℕ) :
    (Finset.univ.image (S.wordRatio n)).card ≤ (n + 1) ^ Fintype.card ι := by
  classical
  have hsub : Finset.univ.image (S.wordRatio n) ⊆
      Finset.univ.image (S.ratioFromCounts n) := by
    intro r hr
    obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hr
    exact Finset.mem_image.mpr
      ⟨wordCountVector n w, Finset.mem_univ _, (S.wordRatio_eq_ratioFromCounts n w).symm.trans hw⟩
  calc
    (Finset.univ.image (S.wordRatio n)).card ≤
        (Finset.univ.image (S.ratioFromCounts n)).card := Finset.card_le_card hsub
    _ ≤ Fintype.card (ι → Fin (n + 1)) := Finset.card_image_le
    _ = (n + 1) ^ Fintype.card ι := by simp

end System
end ExactOverlaps.SelfSimilar
