/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.StoppedWordLaw
public import ExactOverlaps.SelfSimilar.StationaryUniqueness

/-! The coding series factors through the exact observed affine word. -/

@[expose] public section

open MeasureTheory

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι]

theorem coding_word (S : System ι) (n : ℕ) (ω : ℕ → ι) :
    S.coding ω = S.wordMap n (Word.read n ω) (S.coding (Bernoulli.shift^[n] ω)) := by
  induction n generalizing ω with
  | zero => simp only [wordMap_zero, RealSimilarity.identity_apply, Function.iterate_zero_apply]
  | succ n ih =>
    rw [S.coding_shift ω]
    change S.map (ω 0) (S.coding (Bernoulli.shift ω)) =
      ((S.map (ω 0)).comp (S.wordMap n (Word.read n (Bernoulli.shift ω))))
        (S.coding (Bernoulli.shift^[n + 1] ω))
    rw [RealSimilarity.comp_apply, ih (Bernoulli.shift ω), Function.iterate_succ_apply]

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem coding_stoppedWord_suffix_map (S : System ι)
    (T : StoppedConcatenation.BoundedStoppingRule ι) :
    (Bernoulli.sequenceLaw S.alphabetLaw.toMeasure).map
      (fun ω ↦ (T.stoppedWord ω, S.coding (T.suffix ω))) =
        (T.stoppedWordLaw S.alphabetLaw).toMeasure.prod S.codingMeasure := by
  have hT : Measurable T.stoppedWord :=
    T.measurable_stoppedWord.mono T.adapted.measurableSpace_le le_rfl
  have h := congrArg (Measure.map (Prod.map id S.coding))
    (T.stoppedWord_suffix_map S.alphabetLaw.toMeasure)
  rw [Measure.map_map (measurable_id.prodMap S.measurable_coding)
      (hT.prodMk T.measurable_suffix),
    ← Measure.map_prod_map _ _ measurable_id S.measurable_coding, Measure.map_id] at h
  rw [T.stoppedWordLaw_toMeasure]
  exact h

theorem stationary_stoppedWord_product_map (S : System ι)
    (T : StoppedConcatenation.BoundedStoppingRule ι)
    (μ : ProbabilityMeasure ℝ) (hμ : S.IsStationary (μ : Measure ℝ)) :
    ((T.stoppedWordLaw S.alphabetLaw).toMeasure.prod (μ : Measure ℝ)).map
      (fun z ↦ S.wordMap z.1.1 z.1.2 z.2) = (μ : Measure ℝ) := by
  have hm : Measurable (fun z : (Σ n : ℕ, Word ι n) × ℝ ↦ S.wordMap z.1.1 z.1.2 z.2) :=
    measurable_from_prod_countable_right (fun z ↦ (S.wordMap z.1 z.2).measurable)
  rw [S.stationary_eq_codingMeasure (μ : Measure ℝ) hμ, ← S.coding_stoppedWord_suffix_map T]
  have hT : Measurable T.stoppedWord :=
    T.measurable_stoppedWord.mono T.adapted.measurableSpace_le le_rfl
  have hpair : Measurable (fun ω ↦ (T.stoppedWord ω, S.coding (T.suffix ω))) :=
    hT.prodMk (S.measurable_coding.comp T.measurable_suffix)
  rw [Measure.map_map hm hpair]
  change (Bernoulli.sequenceLaw S.alphabetLaw.toMeasure).map
    (fun ω ↦ S.wordMap (T.time ω) (Word.read (T.time ω) ω) (S.coding (T.suffix ω))) = _
  have he : (fun ω ↦ S.wordMap (T.time ω) (Word.read (T.time ω) ω) (S.coding (T.suffix ω))) =
      S.coding := funext (fun ω ↦ (S.coding_word (T.time ω) ω).symm)
  rw [he]
  rfl

end ExactOverlaps.SelfSimilar.System
