/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.StoppedWordLaw
public import ExactOverlaps.StoppedConcatenation.SequentialRules

/-! Two successive stopped words have the actual independent product of their prescribed laws. -/

@[expose] public section

open MeasureTheory

namespace ExactOverlaps

namespace SelfSimilar.Word

variable {ι : Type*}

def concatenate (w v : Σ n : ℕ, Word ι n) : Σ n : ℕ, Word ι n :=
  ⟨v.1 + w.1, append w.1 v.1 w.2 v.2⟩

end SelfSimilar.Word

namespace StoppedConcatenation.BoundedStoppingRule

open SelfSimilar

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

omit [Fintype ι] [MeasurableSingletonClass ι] in
theorem stoppedWord_andThen (T U : BoundedStoppingRule ι) (ω : ℕ → ι) :
    (T.andThen U).stoppedWord ω = Word.concatenate (T.stoppedWord ω) (U.stoppedWord (T.suffix ω)) := by
  change (⟨T.time ω + U.time (T.suffix ω), Word.read (T.time ω + U.time (T.suffix ω)) ω⟩ :
      Σ n : ℕ, Word ι n) =
    ⟨U.time (T.suffix ω) + T.time ω,
      Word.append (T.time ω) (U.time (T.suffix ω))
        (Word.read (T.time ω) ω) (Word.read (U.time (T.suffix ω)) (T.suffix ω))⟩
  rw [Nat.add_comm (T.time ω) (U.time (T.suffix ω))]
  exact congrArg (Sigma.mk _) (Word.read_append (T.time ω) (U.time (T.suffix ω)) ω)

theorem sequential_stoppedWord_map (T U : BoundedStoppingRule ι) (p : PMF ι) :
    (Bernoulli.sequenceLaw p.toMeasure).map
      (fun ω ↦ (T.stoppedWord ω, U.stoppedWord (T.suffix ω))) =
        (Entropy.independentPair (T.stoppedWordLaw p) (U.stoppedWordLaw p)).toMeasure := by
  have hT : Measurable T.stoppedWord :=
    T.measurable_stoppedWord.mono T.adapted.measurableSpace_le le_rfl
  have hU : Measurable U.stoppedWord :=
    U.measurable_stoppedWord.mono U.adapted.measurableSpace_le le_rfl
  rw [Entropy.independentPair_toMeasure, T.stoppedWordLaw_toMeasure, U.stoppedWordLaw_toMeasure]
  have h := congrArg (Measure.map (Prod.map id U.stoppedWord)) (T.stoppedWord_suffix_map p.toMeasure)
  rw [Measure.map_map (measurable_id.prodMap hU) (hT.prodMk T.measurable_suffix),
    ← Measure.map_prod_map _ _ measurable_id hU, Measure.map_id] at h
  exact h

theorem andThen_stoppedWordLaw (T U : BoundedStoppingRule ι) (p : PMF ι) :
    (T.andThen U).stoppedWordLaw p =
      (Entropy.independentPair (T.stoppedWordLaw p) (U.stoppedWordLaw p)).map
        (fun z ↦ Word.concatenate z.1 z.2) := by
  apply PMF.toMeasure_injective
  rw [(T.andThen U).stoppedWordLaw_toMeasure,
    ← PMF.toMeasure_map _ _ (measurable_of_countable _), ← T.sequential_stoppedWord_map U p]
  have hT : Measurable T.stoppedWord :=
    T.measurable_stoppedWord.mono T.adapted.measurableSpace_le le_rfl
  have hU : Measurable U.stoppedWord :=
    U.measurable_stoppedWord.mono U.adapted.measurableSpace_le le_rfl
  have hpair : Measurable (fun ω ↦ (T.stoppedWord ω, U.stoppedWord (T.suffix ω))) :=
    hT.prodMk (hU.comp T.measurable_suffix)
  rw [Measure.map_map (measurable_of_countable _) hpair]
  congr 1
  funext ω
  exact T.stoppedWord_andThen U ω

end StoppedConcatenation.BoundedStoppingRule
end ExactOverlaps
