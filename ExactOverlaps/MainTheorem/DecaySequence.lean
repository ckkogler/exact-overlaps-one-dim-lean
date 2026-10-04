/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.MainTheorem.ReversedBlocks
public import ExactOverlaps.MainTheorem.StoppedTail
public import ExactOverlaps.StoppedConcatenation.Lemma311
public import ExactOverlaps.WFullDimension.Proposition310

/-!
Uniformly improving genuine stopped blocks yield positive scales tending to
zero on which the stationary measure's actual W tends to zero. The block
concatenation is the proved Lemma 3.11, with the independent stationary tail.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace ExactOverlaps.SelfSimilar.System

open MainTheorem StoppedConcatenation ConvolutionDisintegration

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem W_reversed_stopped_blocks_le (S : System ι)
    (μ : ProbabilityMeasure ℝ) (hμ : S.IsStationary (μ : Measure ℝ))
    (T : ℕ → BoundedStoppingRule ι) (r : ℕ → ℝ)
    (hr : ∀ n, 0 < r n) (hanti : StrictAnti r) {κ : ℝ} (hκ : 0 < κ)
    (hcap : ∀ n, meanConditionalMapW ((T n).stoppedWordLaw S.alphabetLaw)
      ((T n).stoppedWordLaw_support_finite S.alphabetLaw)
      S.totalWordRatio S.totalWordTranslation (r n) ≤ Real.exp (-κ))
    (hsep : ∀ n, ∀ w ∈ ((T (n + 1)).stoppedWordLaw S.alphabetLaw).support,
      r (n + 1) < S.rhoMin * r n * |S.wordRatio w.1 w.2|) (n : ℕ) :
    W μ (r n) ≤ Real.exp (-((n : ℝ) * κ * S.rhoMin ^ 2)) := by
  obtain ⟨U, hU, _⟩ := S.exists_stopped_concatenation n
    (fun j ↦ T (n - j)) (fun j ↦ r (n - j)) (fun j ↦ hr (n - j))
    (reversed_stopped_separation_all S T r hanti hsep n)
    (r n) (hr n) (by simp)
  exact (S.W_le_stopped_conditional_average U μ hμ (hr n).le).trans
    (hU.trans (reversed_conditional_product_le S T r hr hκ hcap n))

theorem exists_W_decay_scales_of_improving_stops (S : System ι)
    (μ : ProbabilityMeasure ℝ) (hμ : S.IsStationary (μ : Measure ℝ))
    {κ : ℝ} (hκ : 0 < κ)
    (havail : ∀ ε : ℝ, 0 < ε → ∃ T : BoundedStoppingRule ι, ∃ r : ℝ,
      0 < r ∧ meanConditionalMapW (T.stoppedWordLaw S.alphabetLaw)
        (T.stoppedWordLaw_support_finite S.alphabetLaw)
        S.totalWordRatio S.totalWordTranslation r ≤ Real.exp (-κ) ∧
      ∀ w ∈ (T.stoppedWordLaw S.alphabetLaw).support,
        r < ε * |S.totalWordRatio w|) :
    ∃ r : ℕ → ℝ, (∀ n, 0 < r n) ∧ Tendsto r atTop (𝓝 0) ∧
      Tendsto (fun n ↦ W μ (r n)) atTop (𝓝 0) := by
  obtain ⟨T, r, hr, hcap, hanti, hrzero, hsep⟩ := exists_stopped_scale_sequence S
    (fun T r ↦ meanConditionalMapW (T.stoppedWordLaw S.alphabetLaw)
      (T.stoppedWordLaw_support_finite S.alphabetLaw)
      S.totalWordRatio S.totalWordTranslation r ≤ Real.exp (-κ)) havail
  refine ⟨r, hr, hrzero, ?_⟩
  exact tendsto_zero_of_exponential_cost_bound (fun n ↦ W μ (r n)) hκ
    (pow_pos S.rhoMin_pos 2) (fun n ↦ W_nonneg (hr n).le μ)
    (S.W_reversed_stopped_blocks_le μ hμ T r hr hanti hκ hcap hsep)

theorem dimension_eq_one_of_improving_stops (S : System ι)
    (μ : ProbabilityMeasure ℝ) (hμ : S.IsStationary (μ : Measure ℝ))
    {κ : ℝ} (hκ : 0 < κ)
    (havail : ∀ ε : ℝ, 0 < ε → ∃ T : BoundedStoppingRule ι, ∃ r : ℝ,
      0 < r ∧ meanConditionalMapW (T.stoppedWordLaw S.alphabetLaw)
        (T.stoppedWordLaw_support_finite S.alphabetLaw)
        S.totalWordRatio S.totalWordTranslation r ≤ Real.exp (-κ) ∧
      ∀ w ∈ (T.stoppedWordLaw S.alphabetLaw).support,
        r < ε * |S.totalWordRatio w|) :
    lowerHausdorffDimension (μ : Measure ℝ) = 1 :=
  WFullDimension.proposition_3_10 S μ hμ
    (S.exists_W_decay_scales_of_improving_stops μ hμ hκ havail)

end ExactOverlaps.SelfSimilar.System
