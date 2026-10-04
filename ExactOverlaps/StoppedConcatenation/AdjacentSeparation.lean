/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.WordScalars

/-! Increasing scales turn the source's adjacent separation into the recursive all-pairs form. -/

@[expose] public section

namespace ExactOverlaps.StoppedConcatenation

open SelfSimilar

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem separation_of_adjacent (S : System ι) (m : ℕ)
    (τ : Fin (m + 1) → BoundedStoppingRule ι) (s : Fin (m + 1) → ℝ)
    (hmono : Monotone s)
    (hsep : ∀ i : Fin m, ∀ w ∈ ((τ i.castSucc).stoppedWordLaw S.alphabetLaw).support,
      s i.castSucc ≤ S.rhoMin * s i.succ * |S.totalWordRatio w|) :
    ∀ i j, i < j → ∀ w ∈ ((τ i).stoppedWordLaw S.alphabetLaw).support,
      s i ≤ S.rhoMin * s j * |S.totalWordRatio w| := by
  intro i j hij w hw
  have him : i.val < m := by omega
  let k : Fin m := ⟨i.val, him⟩
  have he : k.castSucc = i := Fin.ext rfl
  have hkj : k.succ ≤ j := by change i.val + 1 ≤ j.val; omega
  have h := hsep k w (he.symm ▸ hw)
  rw [he] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hmono hkj) S.rhoMin_pos.le) (abs_nonneg _))

end ExactOverlaps.StoppedConcatenation
