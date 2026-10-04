module

public import ExactOverlaps.SelfSimilar.RandomWalkEntropy
public import ExactOverlaps.SelfSimilar.JointWordEntropy

/-! Discarding the signed ratio does not change the ordinary random-walk entropy rate. -/

@[expose] public section

open Filter
open scoped Topology

namespace ExactOverlaps.SelfSimilar.System

open Entropy
variable {ι : Type*} [Fintype ι]

theorem jointWordEntropy_sub_translation_le_ratio (S : System ι) (n : ℕ) :
    S.jointWordEntropy n - finiteEntropy (S.wordTranslationLaw n)
      (S.wordTranslationLaw_support_finite n) ≤
      finiteEntropy (S.wordRatioLaw n) (S.wordRatioLaw_support_finite n) := by
  have h := finiteEntropy_pair_map_le (S.wordLaw n) (Set.toFinite _)
    (S.wordTranslation n) (S.wordRatio n)
  change S.jointWordEntropy n ≤ finiteEntropy (S.wordTranslationLaw n)
    (S.wordTranslationLaw_support_finite n) +
    finiteEntropy (S.wordRatioLaw n) (S.wordRatioLaw_support_finite n) at h
  linarith

theorem translationLaw_entropy_le_jointWordEntropy (S : System ι) (n : ℕ) :
    finiteEntropy (S.wordTranslationLaw n) (S.wordTranslationLaw_support_finite n) ≤
      S.jointWordEntropy n := by
  have h := finiteEntropy_map_le (S.jointWordLaw n) (S.jointWordLaw_support_finite n) Prod.fst
  simpa only [S.jointWordLaw_map_fst, jointWordEntropy] using h

theorem jointWordEntropy_sub_translation_div_tendsto_zero (S : System ι) :
    Tendsto (fun n : ℕ ↦ (S.jointWordEntropy n -
      finiteEntropy (S.wordTranslationLaw n) (S.wordTranslationLaw_support_finite n)) / n)
      atTop (𝓝 0) := by
  apply squeeze_zero (fun n ↦ div_nonneg
    (sub_nonneg.mpr (S.translationLaw_entropy_le_jointWordEntropy n)) (Nat.cast_nonneg n))
    (fun n ↦ div_le_div_of_nonneg_right (S.jointWordEntropy_sub_translation_le_ratio n)
      (Nat.cast_nonneg n)) S.wordRatioLaw_entropy_div_tendsto_zero

theorem wordTranslationLaw_entropy_div_tendsto_rate (S : System ι) :
    Tendsto (fun n : ℕ ↦
      finiteEntropy (S.wordTranslationLaw n) (S.wordTranslationLaw_support_finite n) / n)
      atTop (𝓝 S.randomWalkEntropyRate) := by
  have h := S.jointWordEntropy_div_tendsto_rate.sub S.jointWordEntropy_sub_translation_div_tendsto_zero
  convert h using 1
  · funext n
    ring
  · simp

end ExactOverlaps.SelfSimilar.System
