/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.EmbeddedLemma311
public import ExactOverlaps.StoppedConcatenation.EmbeddingEnd
public import ExactOverlaps.StoppedConcatenation.OrderedBlockLawAE
public import ExactOverlaps.StoppedConcatenation.SourceLemma311

/-!
The full concatenation statement: every prescribed stopped block is embedded
at an actual bounded start in the same walk. The blocks have the exact
independent product law, are ordered without overlap almost surely, and end
at the returned terminal rule. All three numerical clauses are retained.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Classical

namespace ExactOverlaps.SelfSimilar.System

open StoppedConcatenation ConvolutionDisintegration

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem lemma311_full (S : System ι) (m : ℕ)
    (τ : Fin (m + 1) → BoundedStoppingRule ι) (s : Fin (m + 1) → ℝ)
    (hs : ∀ j, 0 < s j) (hmono : StrictMono s)
    (hsep : ∀ i : Fin m, ∀ᵐ ω ∂Bernoulli.sequenceLaw S.alphabetLaw.toMeasure,
      s i.castSucc ≤ S.rhoMin * s i.succ * |S.totalWordRatio ((τ i.castSucc).stoppedWord ω)|)
    (μ : ProbabilityMeasure ℝ) (hμ : S.IsStationary (μ : Measure ℝ))
    (r : ℝ) (hr : 0 < r) (hrs : r ≤ s 0) :
    ∃ starts : Fin (m + 1) → BoundedStoppingRule ι, ∃ T : BoundedStoppingRule ι,
      (∀ i : Fin m, ∀ᵐ ω ∂Bernoulli.sequenceLaw S.alphabetLaw.toMeasure,
        ((starts i.castSucc).andThen (τ i.castSucc)).time ω ≤ (starts i.succ).time ω) ∧
      (∀ ω, T.time ω = ((starts (Fin.last m)).andThen (τ (Fin.last m))).time ω) ∧
      iIndepFun (fun j ω ↦ (τ j).stoppedWord ((starts j).suffix ω))
        (Bernoulli.sequenceLaw S.alphabetLaw.toMeasure) ∧
      ((Bernoulli.sequenceLaw S.alphabetLaw.toMeasure).map
        (fun ω j ↦ (τ j).stoppedWord ((starts j).suffix ω)) =
          Measure.pi (fun j ↦ ((τ j).stoppedWordLaw S.alphabetLaw).toMeasure)) ∧
      meanConditionalMapW (T.stoppedWordLaw S.alphabetLaw) (T.stoppedWordLaw_support_finite _)
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
        S.rhoMin * r * |S.totalWordRatio ((τ (Fin.last m)).stoppedWord ((starts (Fin.last m)).suffix ω))| /
          s (Fin.last m) < |S.totalWordRatio (T.stoppedWord ω)| := by
  have hsep' (i : Fin m) := ((τ i.castSucc).stoppedWord_support_iff_ae S.alphabetLaw
    (fun w ↦ s i.castSucc ≤ S.rhoMin * s i.succ * |S.totalWordRatio w|)).mpr (hsep i)
  obtain ⟨A, hW, hA, starts, hlast, horder⟩ := S.exists_stopped_concatenation_embedded_start m τ s hs
    (separation_of_adjacent S m τ s hmono.monotone hsep') r hr hrs
  let T := A.andThen (τ (Fin.last m))
  refine ⟨starts, T, horder, ?_,
    BoundedStoppingRule.independent_ae_ordered_blocks m starts τ S.alphabetLaw horder,
    BoundedStoppingRule.ae_ordered_blocks_joint_map m starts τ S.alphabetLaw horder,
    hW, (S.W_le_stopped_conditional_average T μ hμ hr.le).trans hW, ?_⟩
  · intro ω
    exact ((starts (Fin.last m)).andThen_time_eq_of_time_eq A (τ (Fin.last m)) hlast ω).symm
  · have hAAE := (A.stoppedWord_support_iff_ae S.alphabetLaw
      (fun a ↦ S.rhoMin * r / s (Fin.last m) < |S.totalWordRatio a|)).mp hA
    filter_upwards [hAAE] with ω hω
    have hstart := (starts (Fin.last m)).suffix_eq_of_time_eq A hlast ω
    rw [hstart]
    change S.rhoMin * r * |S.totalWordRatio ((τ (Fin.last m)).stoppedWord (A.suffix ω))| /
      s (Fin.last m) < |S.totalWordRatio ((A.andThen (τ (Fin.last m))).stoppedWord ω)|
    rw [A.stoppedWord_andThen, S.totalWordRatio_concatenate, abs_mul]
    have h := mul_lt_mul_of_pos_right hω
      (abs_pos.mpr (S.totalWordRatio_ne_zero ((τ (Fin.last m)).stoppedWord (A.suffix ω))))
    simpa only [div_mul_eq_mul_div] using h

end ExactOverlaps.SelfSimilar.System
