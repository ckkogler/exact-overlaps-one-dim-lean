/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.SelfSimilar.RatioCounts
public import Mathlib.Data.Fintype.BigOperators

/-!
# Reconstructing a finite digit sum from all but one multiplicity

For an alphabet of size K, a sum of m digit values is determined by K-1
counts in {0,...,m}: the final count is their complement to m. Thus no
arithmetic condition on the digit values is needed for the polynomial bound.
-/

@[expose] public section

noncomputable section
open scoped BigOperators

namespace ExactOverlaps.DigitSums

open SelfSimilar

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The sum of the real values assigned to the letters of a word. -/
def wordSum (v : α → ℝ) : (m : ℕ) → Word α m → ℝ
  | 0, _ => 0
  | m + 1, w => v w.1 + wordSum v m w.2

lemma sum_wordCount (m : ℕ) (w : Word α m) : ∑ a, wordCount m w a = m := by
  induction m with
  | zero => simp [wordCount]
  | succ m ih => simp [wordCount, Finset.sum_add_distrib, ih, Nat.add_comm]

lemma wordSum_eq_sum_count (v : α → ℝ) (m : ℕ) (w : Word α m) :
    wordSum v m w = ∑ a, (wordCount m w a : ℝ) * v a := by
  induction m with
  | zero => simp [wordSum, wordCount]
  | succ m ih =>
    simp [wordSum, wordCount, Nat.cast_add, add_mul, Finset.sum_add_distrib, ih]

/-- Record the multiplicities of all letters other than a distinguished one. -/
def reducedCounts (a₀ : α) (m : ℕ) (w : Word α m) : {a : α // a ≠ a₀} → Fin (m + 1) :=
  fun a ↦ ⟨wordCount m w a, Nat.lt_succ_of_le (wordCount_le m w a)⟩

/-- Recover the digit sum from the reduced multiplicity vector. -/
def sumFromCounts (v : α → ℝ) (a₀ : α) (m : ℕ)
    (c : {a : α // a ≠ a₀} → Fin (m + 1)) : ℝ :=
  (m : ℝ) * v a₀ + ∑ a, ((c a).val : ℝ) * (v a - v a₀)

lemma wordSum_eq_sumFromCounts (v : α → ℝ) (a₀ : α) (m : ℕ) (w : Word α m) :
    wordSum v m w = sumFromCounts v a₀ m (reducedCounts a₀ m w) := by
  have hsum : ∑ a, (wordCount m w a : ℝ) = m := by
    exact_mod_cast sum_wordCount m w
  have hremove : (∑ a, (wordCount m w a : ℝ) * (v a - v a₀)) =
      ∑ a : {a : α // a ≠ a₀}, (wordCount m w a : ℝ) * (v a - v a₀) := by
    rw [Fintype.sum_eq_add_sum_subtype_ne _ a₀]
    simp
  rw [wordSum_eq_sum_count, sumFromCounts]
  change (∑ a, (wordCount m w a : ℝ) * v a) =
    (m : ℝ) * v a₀ + ∑ a : {a : α // a ≠ a₀}, (wordCount m w a : ℝ) * (v a - v a₀)
  rw [← hremove]
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum]
  ring

lemma card_reduced_alphabet (a₀ : α) :
    Fintype.card {a : α // a ≠ a₀} = Fintype.card α - 1 := by
  simp only [ne_eq, Fintype.card_subtype_compl, Fintype.card_unique]

/-- The sharp exponent K-1 in the count of possible sums of m K-valued digits. -/
theorem card_wordSums_le (v : α → ℝ) (a₀ : α) (m : ℕ) :
    (Finset.univ.image (wordSum v m)).card ≤ (m + 1) ^ (Fintype.card α - 1) := by
  classical
  have hsub : Finset.univ.image (wordSum v m) ⊆
      Finset.univ.image (sumFromCounts v a₀ m) := by
    intro x hx
    obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨reducedCounts a₀ m w, Finset.mem_univ _,
      (wordSum_eq_sumFromCounts v a₀ m w).symm.trans hw⟩
  calc
    (Finset.univ.image (wordSum v m)).card ≤
        (Finset.univ.image (sumFromCounts v a₀ m)).card := Finset.card_le_card hsub
    _ ≤ Fintype.card ({a : α // a ≠ a₀} → Fin (m + 1)) := Finset.card_image_le
    _ = (m + 1) ^ (Fintype.card α - 1) := by simp

end ExactOverlaps.DigitSums
