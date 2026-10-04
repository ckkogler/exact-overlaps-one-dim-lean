/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.WImprovement.EnergyScales
public import ExactOverlaps.WImprovement.ConstantStopping
public import ExactOverlaps.WImprovement.SupportTransfer
public import ExactOverlaps.StoppedConcatenation.Lemma311
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Uniform improvement at a genuine bounded stopping time

A strict dimension drop gives one positive exponential improvement before
the relative-scale tolerance is chosen. Both the positive-support and actual
Bernoulli almost-sure conclusions concern the genuine stopped word law.
-/

@[expose] public section

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace ExactOverlaps.SelfSimilar.System

open StoppedConcatenation ConvolutionDisintegration

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem proposition_3_12 (S : System ι)
    (μ : ProbabilityMeasure ℝ) (hμ : S.IsStationary (μ : Measure ℝ))
    (hdim : (lowerHausdorffDimension (μ : Measure ℝ)).toReal <
      min 1 (S.randomWalkEntropyRate / |S.lyapunov|)) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε →
      ∃ T : BoundedStoppingRule ι, ∃ r : ℝ, 0 < r ∧
        meanConditionalMapW (T.stoppedWordLaw S.alphabetLaw) (T.stoppedWordLaw_support_finite _)
          S.totalWordRatio S.totalWordTranslation r ≤ Real.exp (-κ) ∧
        ∀ w ∈ (T.stoppedWordLaw S.alphabetLaw).support, r < ε * |S.totalWordRatio w| := by
  obtain ⟨κ, hκ, hscales⟩ := S.exists_improving_word_scales μ hμ hdim
  refine ⟨κ, hκ, ?_⟩
  intro ε hε
  obtain ⟨N, m, _, hm, s, _, hs, hsep, hcost⟩ := hscales ε hε
  cases m with
  | zero => omega
  | succ m =>
    let τ : Fin (m + 1) → BoundedStoppingRule ι := fun _ ↦ BoundedStoppingRule.constant N
    have hsep' : ∀ i j, i < j → ∀ w ∈ ((τ i).stoppedWordLaw S.alphabetLaw).support,
        s i ≤ S.rhoMin * s j * |S.totalWordRatio w| := by
      intro i j hij w hw
      have hn := S.constant_stoppedWord_support N w hw
      rcases w with ⟨n, w⟩
      dsimp only at hn
      subst n
      exact hsep i j hij w
    obtain ⟨T, hTcost, hTscale⟩ := S.exists_stopped_concatenation m τ s
      (fun i ↦ (hs i).1) hsep' (s 0) (hs 0).1 le_rfl
    refine ⟨T, s 0, (hs 0).1, hTcost.trans ?_, ?_⟩
    · simp only [τ, S.constant_meanConditionalMapW] at hTcost ⊢
      rw [Real.finsetProd_rpow _ _ (fun i _ ↦ S.meanConditionalWordW_nonneg N (hs i).1.le)]
      exact hcost
    · intro w hw
      have h := (hTscale w hw).trans (hs (Fin.last m)).2
      exact (div_lt_iff₀ (abs_pos.mpr (S.totalWordRatio_ne_zero w))).mp h

theorem proposition_3_12_ae (S : System ι)
    (μ : ProbabilityMeasure ℝ) (hμ : S.IsStationary (μ : Measure ℝ))
    (hdim : (lowerHausdorffDimension (μ : Measure ℝ)).toReal <
      min 1 (S.randomWalkEntropyRate / |S.lyapunov|)) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε →
      ∃ T : BoundedStoppingRule ι, ∃ r : ℝ, 0 < r ∧
        meanConditionalMapW (T.stoppedWordLaw S.alphabetLaw) (T.stoppedWordLaw_support_finite _)
          S.totalWordRatio S.totalWordTranslation r ≤ Real.exp (-κ) ∧
        ∀ᵐ ω ∂Bernoulli.sequenceLaw S.alphabetLaw.toMeasure,
          r < ε * |S.prefixRatio (T.time ω) ω| := by
  obtain ⟨κ, hκ, h⟩ := S.proposition_3_12 μ hμ hdim
  refine ⟨κ, hκ, ?_⟩
  intro ε hε
  obtain ⟨T, r, hr, hcost, hsupport⟩ := h ε hε
  exact ⟨T, r, hr, hcost, S.relative_scale_ae_of_support T r ε hsupport⟩

end ExactOverlaps.SelfSimilar.System
