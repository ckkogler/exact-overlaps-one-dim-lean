/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.PairContinuation

/-! Associativity is an equality of actual stopping times and therefore of stopped-word laws. -/

@[expose] public section

open MeasureTheory

namespace ExactOverlaps.StoppedConcatenation.BoundedStoppingRule

open SelfSimilar

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

omit [Fintype ι] [MeasurableSingletonClass ι] in
theorem stoppedWord_eq_of_time_eq (T U : BoundedStoppingRule ι)
    (h : ∀ ω, T.time ω = U.time ω) (ω : ℕ → ι) : T.stoppedWord ω = U.stoppedWord ω := by
  unfold stoppedWord
  rw [h ω]

theorem stoppedWordLaw_eq_of_time_eq (T U : BoundedStoppingRule ι)
    (h : ∀ ω, T.time ω = U.time ω) (p : PMF ι) : T.stoppedWordLaw p = U.stoppedWordLaw p := by
  apply PMF.toMeasure_injective
  rw [T.stoppedWordLaw_toMeasure, U.stoppedWordLaw_toMeasure]
  exact congrArg (Measure.map · _) (funext (T.stoppedWord_eq_of_time_eq U h))

theorem afterPair_andThen_time (T U V : BoundedStoppingRule ι)
    (A : (Σ n : ℕ, Word ι n) × (Σ n : ℕ, Word ι n) → BoundedStoppingRule ι)
    (N : ℕ) (hN : ∀ z, (A z).horizon ≤ N) (ω : ℕ → ι) :
    ((T.afterPair U A N hN).andThen V).time ω =
      (T.afterPair U (fun z ↦ (A z).andThen V) (N + V.horizon)
        (fun z ↦ Nat.add_le_add_right (hN z) V.horizon)).time ω := by
  have hs := (T.andThen U).suffix_andThenChoice
    (fun ω ↦ (T.stoppedWord ω, U.stoppedWord (T.suffix ω)))
    (T.measurable_sequentialWords U) A N hN ω
  change (T.andThen U).time ω +
      (A (T.stoppedWord ω, U.stoppedWord (T.suffix ω))).time ((T.andThen U).suffix ω) +
      V.time ((T.afterPair U A N hN).suffix ω) =
    (T.andThen U).time ω +
      ((A (T.stoppedWord ω, U.stoppedWord (T.suffix ω))).time ((T.andThen U).suffix ω) +
        V.time ((A (T.stoppedWord ω, U.stoppedWord (T.suffix ω))).suffix ((T.andThen U).suffix ω)))
  change (T.afterPair U A N hN).suffix ω = _ at hs
  rw [hs, Nat.add_assoc]

theorem afterPair_andThen_stoppedWordLaw (T U V : BoundedStoppingRule ι)
    (A : (Σ n : ℕ, Word ι n) × (Σ n : ℕ, Word ι n) → BoundedStoppingRule ι)
    (N : ℕ) (hN : ∀ z, (A z).horizon ≤ N) (p : PMF ι) :
    ((T.afterPair U A N hN).andThen V).stoppedWordLaw p =
      (T.afterPair U (fun z ↦ (A z).andThen V) (N + V.horizon)
        (fun z ↦ Nat.add_le_add_right (hN z) V.horizon)).stoppedWordLaw p :=
  stoppedWordLaw_eq_of_time_eq _ _ (T.afterPair_andThen_time U V A N hN) p

end ExactOverlaps.StoppedConcatenation.BoundedStoppingRule
