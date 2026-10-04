module

public import ExactOverlaps.MainTheorem.FiniteAffineTail
public import ExactOverlaps.StoppedConcatenation.StoppedStationarity
public import ExactOverlaps.StoppedConcatenation.WordScalars
public import ExactOverlaps.StoppedConcatenation.ConditionalPushforward

/-!
The stationary-law consequence of the stopped conditional-W estimate.
The independent stationary tail is convolved inside each signed-ratio
class before convexity averages over the actual class probabilities.
-/

@[expose] public section

open MeasureTheory

namespace ExactOverlaps.SelfSimilar.System

open Entropy ConvolutionDisintegration MainTheorem StoppedConcatenation

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem W_le_stopped_conditional_average (S : System ι)
    (T : BoundedStoppingRule ι) (μ : ProbabilityMeasure ℝ)
    (hμ : S.IsStationary (μ : Measure ℝ)) {r : ℝ} (hr : 0 ≤ r) :
    W μ r ≤ meanConditionalMapW (T.stoppedWordLaw S.alphabetLaw)
      (T.stoppedWordLaw_support_finite S.alphabetLaw) S.totalWordRatio S.totalWordTranslation r := by
  let p := T.stoppedWordLaw S.alphabetLaw
  let hp := T.stoppedWordLaw_support_finite S.alphabetLaw
  let := hp.fintype
  have h := W_finite_affine_tail_le (supportLaw p)
    (fun w : p.support ↦ S.wordMap w.val.1 w.val.2) μ hr
  rw [S.stationary_stoppedWord_finiteMix T μ hμ] at h
  have he := meanConditionalMapW_map (supportLaw p) (Set.toFinite _) Subtype.val
    S.totalWordRatio S.totalWordTranslation r
  simp only [supportLaw_map_val] at he
  exact h.trans_eq he.symm

end ExactOverlaps.SelfSimilar.System
