module

public import ExactOverlaps.SelfSimilar.RatioEntropy

/-!
The dyadic partition of the translation coordinate while retaining the exact
signed ratio. Its entropy increments differ from translation-only increments
by at most the ratio entropy, uniformly in the two chosen levels.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ExactOverlaps.SelfSimilar.System

open Entropy
variable {ι : Type*} [Fintype ι]

noncomputable def jointDyadicWordLaw (S : System ι) (n : ℕ) (i : ℤ) : PMF (ℤ × ℝ) :=
  (S.jointWordLaw n).map (fun z ↦ (dyadicQuantize i z.1, z.2))

theorem jointDyadicWordLaw_support_finite (S : System ι) (n : ℕ) (i : ℤ) :
    (S.jointDyadicWordLaw n i).support.Finite := by
  rw [jointDyadicWordLaw, PMF.support_map]
  exact (S.jointWordLaw_support_finite n).image _

theorem jointDyadicWordLaw_map_fst (S : System ι) (n : ℕ) (i : ℤ) :
    (S.jointDyadicWordLaw n i).map Prod.fst =
      dyadicLaw (S.wordTranslationProbability n) i := by
  rw [dyadicLaw_eq_map_of_toMeasure_eq (S.wordTranslationProbability n)
    (S.wordTranslationLaw n) rfl i]
  simp only [jointDyadicWordLaw, jointWordLaw, wordTranslationLaw,
    PMF.map_comp, Function.comp_def]

theorem jointDyadicWordLaw_map_snd (S : System ι) (n : ℕ) (i : ℤ) :
    (S.jointDyadicWordLaw n i).map Prod.snd = S.wordRatioLaw n := by
  simp only [jointDyadicWordLaw, jointWordLaw, wordRatioLaw,
    PMF.map_comp, Function.comp_def]

noncomputable def jointDyadicWordEntropy (S : System ι) (n : ℕ) (i : ℤ) : ℝ :=
  finiteEntropy (S.jointDyadicWordLaw n i) (S.jointDyadicWordLaw_support_finite n i)

theorem translationEntropy_le_jointDyadicWordEntropy (S : System ι) (n : ℕ) (i : ℤ) :
    dyadicEntropy (S.wordTranslationProbability n)
      (S.wordTranslationProbability_hasBoundedSupport n) i ≤ S.jointDyadicWordEntropy n i := by
  have h := finiteEntropy_map_le (S.jointDyadicWordLaw n i)
    (S.jointDyadicWordLaw_support_finite n i) Prod.fst
  simpa only [jointDyadicWordLaw_map_fst, dyadicEntropy, jointDyadicWordEntropy] using h

theorem jointDyadicWordEntropy_le_translation_add_ratio (S : System ι) (n : ℕ) (i : ℤ) :
    S.jointDyadicWordEntropy n i ≤
      dyadicEntropy (S.wordTranslationProbability n)
        (S.wordTranslationProbability_hasBoundedSupport n) i +
      finiteEntropy (S.wordRatioLaw n) (S.wordRatioLaw_support_finite n) := by
  have h := finiteEntropy_pair_map_le (S.jointDyadicWordLaw n i)
    (S.jointDyadicWordLaw_support_finite n i) Prod.fst Prod.snd
  have he : (fun z : ℤ × ℝ ↦ (z.1, z.2)) = id := rfl
  simpa only [he, PMF.map_id, jointDyadicWordLaw_map_fst, jointDyadicWordLaw_map_snd,
    jointDyadicWordEntropy, dyadicEntropy] using h

theorem abs_joint_increment_sub_translation_increment_le (S : System ι)
    (n : ℕ) (i j : ℤ) :
    |(S.jointDyadicWordEntropy n j - S.jointDyadicWordEntropy n i) -
      (dyadicEntropy (S.wordTranslationProbability n)
          (S.wordTranslationProbability_hasBoundedSupport n) j -
        dyadicEntropy (S.wordTranslationProbability n)
          (S.wordTranslationProbability_hasBoundedSupport n) i)| ≤
      finiteEntropy (S.wordRatioLaw n) (S.wordRatioLaw_support_finite n) := by
  have hi0 := S.translationEntropy_le_jointDyadicWordEntropy n i
  have hi1 := S.jointDyadicWordEntropy_le_translation_add_ratio n i
  have hj0 := S.translationEntropy_le_jointDyadicWordEntropy n j
  have hj1 := S.jointDyadicWordEntropy_le_translation_add_ratio n j
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Recording the ratio has vanishing cost for arbitrary sequences of fine and coarse levels. -/
theorem joint_increment_error_div_tendsto_zero (S : System ι) (i j : ℕ → ℤ) :
    Tendsto (fun n : ℕ ↦
      ((S.jointDyadicWordEntropy n (j n) - S.jointDyadicWordEntropy n (i n)) -
        (dyadicEntropy (S.wordTranslationProbability n)
            (S.wordTranslationProbability_hasBoundedSupport n) (j n) -
          dyadicEntropy (S.wordTranslationProbability n)
            (S.wordTranslationProbability_hasBoundedSupport n) (i n))) / n)
      atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun n ↦ ?_) (S.wordRatioLaw_entropy_div_tendsto_zero)
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)]
  exact div_le_div_of_nonneg_right
    (S.abs_joint_increment_sub_translation_increment_le n (i n) (j n)) (Nat.cast_nonneg n)

end ExactOverlaps.SelfSimilar.System
