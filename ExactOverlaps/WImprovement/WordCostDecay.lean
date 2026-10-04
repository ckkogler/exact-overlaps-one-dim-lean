/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.WImprovement.CostDecay
public import ExactOverlaps.WImprovement.WordVarianceProfiles

/-! Exact decay for the actual word translation law conditional on its signed ratio. -/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace ExactOverlaps.SelfSimilar.System

open Entropy FiniteProbability ConvolutionDisintegration WImprovement

variable {ι : Type*} [Fintype ι]

theorem meanConditionalWordW_eq_sum (S : System ι) (n : ℕ) (r : ℝ) :
    meanConditionalMapW (S.wordLaw n) (Set.toFinite _)
      (S.wordRatio n) (S.wordTranslation n) r =
      (letI : Fintype (S.wordRatioLaw n).support := (S.wordRatioLaw_support_finite n).fintype
      ∑ t : (S.wordRatioLaw n).support,
        (supportLaw (S.wordRatioLaw n) t).toReal * W (pmfLaw (S.ratioTranslationLaw n t)) r) := by
  rw [meanConditionalMapW, meanFiberFunctional_eq_sum]
  rfl

theorem meanConditionalWordW_nonneg (S : System ι) (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ meanConditionalMapW (S.wordLaw n) (Set.toFinite _)
      (S.wordRatio n) (S.wordTranslation n) r := by
  rw [S.meanConditionalWordW_eq_sum]
  exact Finset.sum_nonneg (fun _ _ ↦ mul_nonneg ENNReal.toReal_nonneg (W_nonneg hr _))

theorem meanConditionalWordW_le_profile (S : System ι) (n : ℕ) {r : ℝ} (hr : 0 < r) :
    meanConditionalMapW (S.wordLaw n) (Set.toFinite _)
      (S.wordRatio n) (S.wordTranslation n) r ≤
      1 - (1 - Real.exp (-1)) * S.meanRatioVarianceProfile n r := by
  let : Fintype (S.wordRatioLaw n).support := (S.wordRatioLaw_support_finite n).fintype
  rw [S.meanConditionalWordW_eq_sum]
  exact meanW_le_one_sub_profile (supportLaw (S.wordRatioLaw n)) (S.ratioTranslationLaw n) hr

theorem product_conditionalWordW_decay (S : System ι) (n m : ℕ) (s : Fin m → ℝ)
    (hs : ∀ i, 0 < s i) {a η : ℝ} (ha : 0 ≤ a)
    (hsum : η ≤ ∑ i, S.meanRatioVarianceProfile n (s i)) :
    (∏ i, meanConditionalMapW (S.wordLaw n) (Set.toFinite _)
      (S.wordRatio n) (S.wordTranslation n) (s i)) ^ a ≤
      Real.exp (-a * (1 - Real.exp (-1)) * η) := by
  exact product_decay_of_profile_sum _ _
    (fun i ↦ S.meanConditionalWordW_nonneg n (hs i).le)
    (fun i ↦ S.meanConditionalWordW_le_profile n (hs i)) ha hsum

end ExactOverlaps.SelfSimilar.System
