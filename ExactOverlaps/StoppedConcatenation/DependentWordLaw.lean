/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.DependentRules
public import ExactOverlaps.StoppedConcatenation.DependentBlockLaw
public import ExactOverlaps.StoppedConcatenation.SequentialWordLaw

/-! The law of an observed-word-dependent continuation is its actual kernel mixture. -/

@[expose] public section

open MeasureTheory

namespace ExactOverlaps.StoppedConcatenation.BoundedStoppingRule

open SelfSimilar

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

def afterWord (T : BoundedStoppingRule ι) (U : (Σ n : ℕ, Word ι n) → BoundedStoppingRule ι)
    (N : ℕ) (hN : ∀ w, (U w).horizon ≤ N) : BoundedStoppingRule ι :=
  T.andThenChoice T.stoppedWord T.measurable_stoppedWord U N hN

theorem stoppedWord_afterWord (T : BoundedStoppingRule ι)
    (U : (Σ n : ℕ, Word ι n) → BoundedStoppingRule ι) (N : ℕ)
    (hN : ∀ w, (U w).horizon ≤ N) (ω : ℕ → ι) :
    (T.afterWord U N hN).stoppedWord ω =
      Word.concatenate (T.stoppedWord ω) ((U (T.stoppedWord ω)).stoppedWord (T.suffix ω)) := by
  change (⟨T.time ω + (U (T.stoppedWord ω)).time (T.suffix ω),
      Word.read (T.time ω + (U (T.stoppedWord ω)).time (T.suffix ω)) ω⟩ : Σ n, Word ι n) = _
  rw [Nat.add_comm (T.time ω)]
  exact congrArg (Sigma.mk _) (Word.read_append (T.time ω) ((U (T.stoppedWord ω)).time (T.suffix ω)) ω)

theorem dependent_stoppedWord_map (T : BoundedStoppingRule ι)
    (U : (Σ n : ℕ, Word ι n) → BoundedStoppingRule ι) (p : PMF ι) :
    (Bernoulli.sequenceLaw p.toMeasure).map
      (fun ω ↦ (T.stoppedWord ω, (U (T.stoppedWord ω)).stoppedWord (T.suffix ω))) =
        (Entropy.jointMixture (T.stoppedWordLaw p) (fun w ↦ (U w).stoppedWordLaw p)).toMeasure := by
  apply T.dependent_observable_map p.toMeasure T.stoppedWord T.measurable_stoppedWord
    (fun w ↦ (U w).stoppedWord)
  · intro w
    exact (U w).measurable_stoppedWord.mono (U w).adapted.measurableSpace_le le_rfl
  · exact (T.stoppedWordLaw_toMeasure p).symm
  · intro w
    exact ((U w).stoppedWordLaw_toMeasure p).symm

theorem afterWord_stoppedWordLaw (T : BoundedStoppingRule ι)
    (U : (Σ n : ℕ, Word ι n) → BoundedStoppingRule ι) (N : ℕ)
    (hN : ∀ w, (U w).horizon ≤ N) (p : PMF ι) :
    (T.afterWord U N hN).stoppedWordLaw p =
      (Entropy.jointMixture (T.stoppedWordLaw p) (fun w ↦ (U w).stoppedWordLaw p)).map
        (fun z ↦ Word.concatenate z.1 z.2) := by
  apply PMF.toMeasure_injective
  rw [(T.afterWord U N hN).stoppedWordLaw_toMeasure,
    ← PMF.toMeasure_map _ _ (measurable_of_countable _), ← T.dependent_stoppedWord_map U p]
  have hT : Measurable T.stoppedWord :=
    T.measurable_stoppedWord.mono T.adapted.measurableSpace_le le_rfl
  have hG : Measurable (fun z : (Σ n : ℕ, Word ι n) × (ℕ → ι) ↦ (U z.1).stoppedWord z.2) :=
    measurable_from_prod_countable_right (fun w ↦
      (U w).measurable_stoppedWord.mono (U w).adapted.measurableSpace_le le_rfl)
  have hpair : Measurable (fun ω ↦
      (T.stoppedWord ω, (U (T.stoppedWord ω)).stoppedWord (T.suffix ω))) :=
    hT.prodMk (hG.comp (hT.prodMk T.measurable_suffix))
  rw [Measure.map_map (measurable_of_countable _) hpair]
  congr 1
  funext ω
  exact T.stoppedWord_afterWord U N hN ω

end ExactOverlaps.StoppedConcatenation.BoundedStoppingRule
