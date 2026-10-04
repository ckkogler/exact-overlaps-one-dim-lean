/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.Lemma311
public import ExactOverlaps.StoppedConcatenation.AdjacentSeparation
public import ExactOverlaps.MainTheorem.StoppedTail
public import ExactOverlaps.StoppedConcatenation.SupportAE

/-!
The three clauses of Lemma 3.11 under its adjacent scale-separation hypothesis.
The final ratio retains the actual last stopped block in the same Bernoulli walk.
-/

@[expose] public section

open MeasureTheory
open scoped Classical

namespace ExactOverlaps.SelfSimilar.System

open StoppedConcatenation ConvolutionDisintegration

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem lemma311 (S : System ι) (m : ℕ)
    (τ : Fin (m + 1) → BoundedStoppingRule ι) (s : Fin (m + 1) → ℝ)
    (hs : ∀ j, 0 < s j) (hmono : StrictMono s)
    (hsep : ∀ i : Fin m, ∀ᵐ ω ∂Bernoulli.sequenceLaw S.alphabetLaw.toMeasure,
      s i.castSucc ≤ S.rhoMin * s i.succ * |S.totalWordRatio ((τ i.castSucc).stoppedWord ω)|)
    (μ : ProbabilityMeasure ℝ) (hμ : S.IsStationary (μ : Measure ℝ))
    (r : ℝ) (hr : 0 < r) (hrs : r ≤ s 0) :
    ∃ A : BoundedStoppingRule ι,
      meanConditionalMapW ((A.andThen (τ (Fin.last m))).stoppedWordLaw S.alphabetLaw)
        ((A.andThen (τ (Fin.last m))).stoppedWordLaw_support_finite _)
        S.totalWordRatio S.totalWordTranslation r ≤
          ∏ j : Fin (m + 1),
            (meanConditionalMapW ((τ j).stoppedWordLaw S.alphabetLaw)
              ((τ j).stoppedWordLaw_support_finite _) S.totalWordRatio S.totalWordTranslation (s j)) ^
                (S.rhoMin ^ 2) ∧
      W μ r ≤ ∏ j : Fin (m + 1),
        (meanConditionalMapW ((τ j).stoppedWordLaw S.alphabetLaw)
          ((τ j).stoppedWordLaw_support_finite _) S.totalWordRatio S.totalWordTranslation (s j)) ^
            (S.rhoMin ^ 2) ∧
      ∀ᵐ ω ∂Bernoulli.sequenceLaw S.alphabetLaw.toMeasure,
        S.rhoMin * r * |S.totalWordRatio ((τ (Fin.last m)).stoppedWord (A.suffix ω))| /
          s (Fin.last m) < |S.totalWordRatio ((A.andThen (τ (Fin.last m))).stoppedWord ω)| := by
  have hsep' (i : Fin m) := ((τ i.castSucc).stoppedWord_support_iff_ae S.alphabetLaw
    (fun w ↦ s i.castSucc ≤ S.rhoMin * s i.succ * |S.totalWordRatio w|)).mpr (hsep i)
  obtain ⟨A, hW, hA⟩ := S.exists_stopped_concatenation_start m τ s hs
    (separation_of_adjacent S m τ s hmono.monotone hsep') r hr hrs
  refine ⟨A, hW, (S.W_le_stopped_conditional_average (A.andThen (τ (Fin.last m))) μ hμ hr.le).trans hW, ?_⟩
  have hAAE := (A.stoppedWord_support_iff_ae S.alphabetLaw
    (fun a ↦ S.rhoMin * r / s (Fin.last m) < |S.totalWordRatio a|)).mp hA
  filter_upwards [hAAE] with ω hω
  rw [A.stoppedWord_andThen, S.totalWordRatio_concatenate, abs_mul]
  have h := mul_lt_mul_of_pos_right hω
    (abs_pos.mpr (S.totalWordRatio_ne_zero ((τ (Fin.last m)).stoppedWord (A.suffix ω))))
  simpa only [div_mul_eq_mul_div] using h

end ExactOverlaps.SelfSimilar.System
