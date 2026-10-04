/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.CodingWord
public import ExactOverlaps.StoppedConcatenation.FiniteAffineMixtures
public import ExactOverlaps.StoppedConcatenation.FiniteWJensen

/-! Genuine finite stationary decompositions and W bounds at every bounded stopping time. -/

@[expose] public section

open MeasureTheory

namespace ExactOverlaps.SelfSimilar.System

open ConvolutionDisintegration Entropy

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem stationary_stoppedWord_finiteMix (S : System ι)
    (T : StoppedConcatenation.BoundedStoppingRule ι)
    (μ : ProbabilityMeasure ℝ) (hμ : S.IsStationary (μ : Measure ℝ)) :
    (letI := (T.stoppedWordLaw_support_finite S.alphabetLaw).fintype
     finiteMix (supportLaw (T.stoppedWordLaw S.alphabetLaw))
       (fun w ↦ μ.map (S.wordMap w.val.1 w.val.2))) = μ := by
  let := (T.stoppedWordLaw_support_finite S.alphabetLaw).fintype
  apply ProbabilityMeasure.toMeasure_injective
  exact (finite_support_affine_product_map (T.stoppedWordLaw S.alphabetLaw)
    (T.stoppedWordLaw_support_finite S.alphabetLaw) μ (fun w ↦ S.wordMap w.1 w.2)).symm.trans
    (S.stationary_stoppedWord_product_map T μ hμ)

theorem W_le_stoppedWord_average (S : System ι)
    (T : StoppedConcatenation.BoundedStoppingRule ι)
    (μ : ProbabilityMeasure ℝ) (hμ : S.IsStationary (μ : Measure ℝ))
    {r : ℝ} (hr : 0 ≤ r) :
    W μ r ≤
      (letI := (T.stoppedWordLaw_support_finite S.alphabetLaw).fintype
       ∑ w : (T.stoppedWordLaw S.alphabetLaw).support,
         (T.stoppedWordLaw S.alphabetLaw w).toReal * W (μ.map (S.wordMap w.val.1 w.val.2)) r) := by
  let := (T.stoppedWordLaw_support_finite S.alphabetLaw).fintype
  have h := W_finiteMix_le (supportLaw (T.stoppedWordLaw S.alphabetLaw))
    (fun w ↦ μ.map (S.wordMap w.val.1 w.val.2)) hr
  rw [S.stationary_stoppedWord_finiteMix T μ hμ] at h
  exact h

end ExactOverlaps.SelfSimilar.System
