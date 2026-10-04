/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.WImprovement.Parameters
public import ExactOverlaps.WImprovement.WordCostDecay
public import ExactOverlaps.SelfSimilar.Corollary34
public import ExactOverlaps.StoppedConcatenation.WordScalars

/-!
# Uniformly improving finite word scales

The dimension drop supplies one positive contraction exponent before the
relative-scale tolerance is chosen. The sampled scales satisfy separation
for every word, including listed words of probability zero.
-/

@[expose] public section

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace ExactOverlaps.SelfSimilar.System

open WImprovement ConvolutionDisintegration

variable {ι : Type*} [Fintype ι]

theorem exists_improving_word_scales (S : System ι)
    (μ : ProbabilityMeasure ℝ) (hμ : S.IsStationary (μ : Measure ℝ))
    (hdim : (lowerHausdorffDimension (μ : Measure ℝ)).toReal <
      min 1 (S.randomWalkEntropyRate / |S.lyapunov|)) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε →
      ∃ N m : ℕ, 1 < N ∧ 0 < m ∧ ∃ s : Fin m → ℝ, StrictMono s ∧
        (∀ i, 0 < s i ∧ s i / S.rhoMin ^ (N + 1) < ε) ∧
        (∀ i j, i < j → ∀ w : Word ι N,
          s i ≤ S.rhoMin * s j * |S.wordRatio N w|) ∧
        (∏ i, meanConditionalMapW (S.wordLaw N) (Set.toFinite _)
          (S.wordRatio N) (S.wordTranslation N) (s i)) ^ (S.rhoMin ^ 2) ≤
          Real.exp (-κ) := by
  obtain ⟨η, hη, henergy⟩ := S.corollary_3_4 μ hμ hdim
  let L := Real.log S.rhoMin⁻¹
  have hL : 0 < L := log_inv_pos S.rhoMin_pos S.rhoMin_lt_one
  let η₀ := η / (2 * L)
  have hη₀ : 0 < η₀ := div_pos hη (by positivity)
  let κ := S.rhoMin ^ 2 * (1 - Real.exp (-1)) * η₀
  have hκ : 0 < κ := mul_pos (mul_pos (pow_pos S.rhoMin_pos 2) varianceDecay_pos) hη₀
  refine ⟨κ, hκ, ?_⟩
  intro ε hε
  let C := max (Real.exp |S.lyapunov|) S.rhoMin⁻¹ + 1
  have hCχ : Real.exp |S.lyapunov| < C := by
    have h := le_max_left (Real.exp |S.lyapunov|) S.rhoMin⁻¹
    dsimp [C]
    linarith
  have hCρ : S.rhoMin⁻¹ < C := by
    have h := le_max_right (Real.exp |S.lyapunov|) S.rhoMin⁻¹
    dsimp [C]
    linarith
  have hC : 0 < C := (Real.exp_pos _).trans hCχ
  have hCρ1 : 1 < C * S.rhoMin := by
    have h := mul_lt_mul_of_pos_right hCρ S.rhoMin_pos
    simpa only [inv_mul_cancel₀ S.rhoMin_pos.ne'] using h
  have hsmall := (relative_scale_tendsto_zero S.rhoMin_pos hCρ1).eventually
    (gt_mem_nhds hε)
  obtain ⟨N, hN, hNE, hsmallN⟩ :=
    ((eventually_gt_atTop 1).and ((henergy C hCχ).and hsmall)).exists
  let d := ((N : ℝ) + 1) * L
  have hd : 0 < d := mul_pos (by positivity) hL
  have hmargin : d * η₀ < S.meanRatioTranslationEnergy N (C ^ (-(N : ℤ))) :=
    (sampling_margin hη hL hN).trans_le hNE
  obtain ⟨m, hm, s, hs, hsR, hsep, hsum⟩ :=
    S.exists_ratio_variance_scales N (zpow_pos hC _) hd hη₀.le hmargin
  refine ⟨N, m, hN, hm, s, hs, ?_, ?_, ?_⟩
  · intro i
    exact ⟨(hsR i).1, (div_lt_div_of_pos_right (hsR i).2
      (pow_pos S.rhoMin_pos (N + 1))).trans hsmallN⟩
  · intro i j hij w
    have hdiv := separation_division S.rhoMin_pos N (hsep i j hij)
    have hbase := (div_le_iff₀ (pow_pos S.rhoMin_pos N)).mp hdiv
    exact hbase.trans (mul_le_mul_of_nonneg_left (S.rhoMin_pow_le_abs_wordRatio N w)
      (mul_nonneg S.rhoMin_pos.le (hsR j).1.le))
  · have h := S.product_conditionalWordW_decay N m s (fun i ↦ (hsR i).1)
      (sq_nonneg S.rhoMin) hsum.le
    simpa only [κ, neg_mul] using h

end ExactOverlaps.SelfSimilar.System
