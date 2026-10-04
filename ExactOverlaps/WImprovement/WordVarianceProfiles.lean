/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.WImprovement.LogProfileSampling
public import ExactOverlaps.SelfSimilar.ConditionalMapEnergy

/-!
# Variance profiles conditional on the actual signed word ratio

The profile uses exactly the positive-mass ratio classes and their actual
probabilities. The separated-scale sampling theorem therefore applies
directly to the proved ratio-conditioned energy supply.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace ExactOverlaps.SelfSimilar.System

open Entropy VarianceEnergy WImprovement

variable {ι : Type*} [Fintype ι]

def meanRatioVarianceProfile (S : System ι) (n : ℕ) (r : ℝ) : ℝ :=
  let : Fintype (S.wordRatioLaw n).support := (S.wordRatioLaw_support_finite n).fintype
  meanVarianceProfile (supportLaw (S.wordRatioLaw n)) (S.ratioTranslationLaw n) r

lemma meanRatioVarianceProfile_nonneg (S : System ι) (n : ℕ) (r : ℝ) :
    0 ≤ S.meanRatioVarianceProfile n r := by
  let : Fintype (S.wordRatioLaw n).support := (S.wordRatioLaw_support_finite n).fintype
  exact meanVarianceProfile_nonneg _ _ _

lemma meanRatioVarianceProfile_le_one (S : System ι) (n : ℕ) {r : ℝ} (hr : 0 < r) :
    S.meanRatioVarianceProfile n r ≤ 1 := by
  let : Fintype (S.wordRatioLaw n).support := (S.wordRatioLaw_support_finite n).fintype
  exact meanVarianceProfile_le_one _ _ hr

theorem exists_ratio_variance_scales (S : System ι) (n : ℕ)
    {R d η : ℝ} (hR : 0 < R) (hd : 0 < d) (hη : 0 ≤ η)
    (henergy : d * η < S.meanRatioTranslationEnergy n R) :
    ∃ m : ℕ, 0 < m ∧ ∃ s : Fin m → ℝ, StrictMono s ∧
      (∀ i, 0 < s i ∧ s i < R) ∧
      (∀ i j, i < j → Real.exp d * s i ≤ s j) ∧
      η < ∑ i, S.meanRatioVarianceProfile n (s i) := by
  let : Fintype (S.wordRatioLaw n).support := (S.wordRatioLaw_support_finite n).fintype
  rw [S.meanRatioTranslationEnergy_eq_sum] at henergy
  have hE : d * η < ∑ i : (S.wordRatioLaw n).support,
      (supportLaw (S.wordRatioLaw n) i).toReal *
        (energyBelow (S.ratioTranslationLaw n i).toMeasure R).toReal := by
    simpa only [supportLaw_apply] using henergy
  exact exists_separated_variance_scales (supportLaw (S.wordRatioLaw n))
    (S.ratioTranslationLaw n) (S.ratioTranslationLaw_support_finite n) hR hd hη hE

end ExactOverlaps.SelfSimilar.System
