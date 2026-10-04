/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.WordMeasurability

/-! Equality of word observations is exactly agreement of the observed symbols. -/

@[expose] public section

namespace ExactOverlaps.SelfSimilar.Word

variable {ι : Type*}

theorem prefix_eq_of_read_eq (n : ℕ) {ω ω' : ℕ → ι} (h : read n ω = read n ω') :
    ∀ k < n, ω k = ω' k := by
  induction n generalizing ω ω' with
  | zero => intro k hk; omega
  | succ n ih =>
    change (ω 0, read n (Bernoulli.shift ω)) = (ω' 0, read n (Bernoulli.shift ω')) at h
    intro k hk
    cases k with
    | zero => exact congrArg Prod.fst h
    | succ k => exact ih (congrArg Prod.snd h) k (by omega)

theorem read_eq_iff_prefix_eq (n : ℕ) (ω ω' : ℕ → ι) :
    read n ω = read n ω' ↔ ∀ k < n, ω k = ω' k :=
  ⟨prefix_eq_of_read_eq n, read_eq_of_prefix_eq n⟩

end ExactOverlaps.SelfSimilar.Word
