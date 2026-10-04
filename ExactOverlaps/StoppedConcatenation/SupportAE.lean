/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.StoppedWordLaw

/-! Almost-sure stopped-word properties are exactly properties on its true positive-mass support. -/

@[expose] public section

open MeasureTheory

namespace ExactOverlaps.StoppedConcatenation.BoundedStoppingRule

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem stoppedWord_support_iff_ae (T : BoundedStoppingRule ι) (p : PMF ι)
    (P : (Σ n : ℕ, SelfSimilar.Word ι n) → Prop) :
    (∀ w ∈ (T.stoppedWordLaw p).support, P w) ↔
      ∀ᵐ ω ∂Bernoulli.sequenceLaw p.toMeasure, P (T.stoppedWord ω) := by
  have hset : MeasurableSet {w | P w} := (Set.to_countable _).measurableSet
  have he : (∀ w ∈ (T.stoppedWordLaw p).support, P w) ↔
      ∀ᵐ w ∂(T.stoppedWordLaw p).toMeasure, P w := by
    change (T.stoppedWordLaw p).support ⊆ {w | P w} ↔
      {w | P w} ∈ ae (T.stoppedWordLaw p).toMeasure
    rw [mem_ae_iff_prob_eq_one hset, PMF.toMeasure_apply_eq_one_iff _ hset]
  rw [he, T.stoppedWordLaw_toMeasure]
  exact ae_map_iff
    (T.measurable_stoppedWord.mono T.adapted.measurableSpace_le le_rfl).aemeasurable hset

end ExactOverlaps.StoppedConcatenation.BoundedStoppingRule
