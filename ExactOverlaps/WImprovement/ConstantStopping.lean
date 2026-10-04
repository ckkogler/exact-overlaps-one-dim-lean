/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.ConditionalPushforward
public import ExactOverlaps.StoppedConcatenation.WordScalars

/-! A deterministic word block is exactly the corresponding genuine stopped word law. -/

@[expose] public section

noncomputable section
open MeasureTheory

namespace ExactOverlaps.SelfSimilar.System

open StoppedConcatenation ConvolutionDisintegration

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem constant_stoppedWordLaw (S : System ι) (n : ℕ) :
    (BoundedStoppingRule.constant n).stoppedWordLaw S.alphabetLaw =
      (S.wordLaw n).map (Sigma.mk n) := by
  apply PMF.toMeasure_injective
  rw [BoundedStoppingRule.stoppedWordLaw_toMeasure,
    ← PMF.toMeasure_map _ _ (measurable_of_finite _), ← S.bernoulli_read_map n,
    Measure.map_map (measurable_of_finite _) (Word.measurable_read n)]
  rfl

theorem constant_stoppedWord_support (S : System ι) (n : ℕ)
    (z : Σ n : ℕ, Word ι n)
    (hz : z ∈ ((BoundedStoppingRule.constant n).stoppedWordLaw S.alphabetLaw).support) :
    z.1 = n := by
  rw [S.constant_stoppedWordLaw] at hz
  obtain ⟨w, _, hw⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
  exact (congrArg Sigma.fst hw).symm

theorem constant_meanConditionalMapW (S : System ι) (n : ℕ) (r : ℝ) :
    meanConditionalMapW ((BoundedStoppingRule.constant n).stoppedWordLaw S.alphabetLaw)
      (BoundedStoppingRule.stoppedWordLaw_support_finite _ _)
      S.totalWordRatio S.totalWordTranslation r =
      meanConditionalMapW (S.wordLaw n) (Set.toFinite _)
        (S.wordRatio n) (S.wordTranslation n) r := by
  have he := FiniteProbability.finiteFunctional_congr
    (fun q hq ↦ meanConditionalMapW q hq S.totalWordRatio S.totalWordTranslation r)
    (S.constant_stoppedWordLaw n)
    (BoundedStoppingRule.stoppedWordLaw_support_finite _ _)
    (show ((S.wordLaw n).map (Sigma.mk n)).support.Finite from by
      simpa using (Set.toFinite (S.wordLaw n).support).image (Sigma.mk n))
  exact he.trans (meanConditionalMapW_map (S.wordLaw n) (Set.toFinite _)
    (Sigma.mk n) S.totalWordRatio S.totalWordTranslation r)

end ExactOverlaps.SelfSimilar.System
