module

public import ExactOverlaps.SelfSimilar.HochmanTheorem14
public import ExactOverlaps.SelfSimilar.LyapunovEntropyApproximation

/-! Absolute coarse and fine entropy limits for the actual random word law. -/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ExactOverlaps.SelfSimilar.System

open Entropy
variable {ι : Type*} [Fintype ι]

theorem contractionScale_exp_lyapunov_eq (S : System ι) (n : ℕ) :
    contractionScale (Real.exp S.lyapunov) n = targetRatioLevel S.dyadicLyapunov 1 n := by
  unfold contractionScale targetRatioLevel dyadicLyapunov
  rw [Real.log_exp]
  congr 1
  ring

theorem wordTranslationEntropy_coarse_div_tendsto (S : System ι)
    (μ : ProbabilityMeasure ℝ) (hμ : S.IsStationary (μ : Measure ℝ)) :
    Tendsto (fun n : ℕ ↦ dyadicEntropy (S.wordTranslationProbability n)
      (S.wordTranslationProbability_hasBoundedSupport n)
      (targetRatioLevel S.dyadicLyapunov 1 n) / n) atTop
      (𝓝 ((-S.lyapunov) * (lowerHausdorffDimension (μ : Measure ℝ)).toReal)) := by
  have hstat := S.dyadicEntropy_level_div_tendsto_dimension μ hμ S.dyadicLyapunov_pos
    (by simpa only [one_mul] using targetRatioLevel_div_tendsto S.dyadicLyapunov 1)
  have herr := S.lyapunov_entropy_error_div_tendsto_zero μ hμ
  simp only [S.contractionScale_exp_lyapunov_eq] at herr
  have hvalue : (lowerHausdorffDimension (μ : Measure ℝ)).toReal * S.dyadicLyapunov *
      Real.log 2 = (-S.lyapunov) * (lowerHausdorffDimension (μ : Measure ℝ)).toReal := by
    dsimp [dyadicLyapunov]
    have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    field_simp [hlog]
  convert hstat.sub herr using 1
  · funext n
    ring
  · simp only [sub_zero, hvalue]

theorem joint_minus_translation_div_tendsto_zero (S : System ι) (i : ℕ → ℤ) :
    Tendsto (fun n : ℕ ↦ (S.jointDyadicWordEntropy n (i n) -
      dyadicEntropy (S.wordTranslationProbability n)
        (S.wordTranslationProbability_hasBoundedSupport n) (i n)) / n) atTop (𝓝 0) := by
  apply squeeze_zero (fun n ↦ div_nonneg
    (sub_nonneg.mpr (S.translationEntropy_le_jointDyadicWordEntropy n (i n)))
    (Nat.cast_nonneg n)) _ S.wordRatioLaw_entropy_div_tendsto_zero
  intro n
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  linarith [S.jointDyadicWordEntropy_le_translation_add_ratio n (i n)]

theorem jointDyadicWordEntropy_coarse_div_tendsto (S : System ι)
    (μ : ProbabilityMeasure ℝ) (hμ : S.IsStationary (μ : Measure ℝ)) :
    Tendsto (fun n : ℕ ↦ S.jointDyadicWordEntropy n
      (targetRatioLevel S.dyadicLyapunov 1 n) / n) atTop
      (𝓝 ((-S.lyapunov) * (lowerHausdorffDimension (μ : Measure ℝ)).toReal)) := by
  have h := (S.joint_minus_translation_div_tendsto_zero (targetRatioLevel S.dyadicLyapunov 1)).add
    (S.wordTranslationEntropy_coarse_div_tendsto μ hμ)
  convert h using 1
  · funext n
    ring
  · simp

theorem wordTranslationEntropy_fine_div_tendsto (S : System ι)
    (μ : ProbabilityMeasure ℝ) (hμ : S.IsStationary (μ : Measure ℝ))
    (hdim : (lowerHausdorffDimension (μ : Measure ℝ)).toReal < 1)
    {q : ℝ} (hq : 1 < q) :
    Tendsto (fun n : ℕ ↦ dyadicEntropy (S.wordTranslationProbability n)
      (S.wordTranslationProbability_hasBoundedSupport n)
      (targetRatioLevel S.dyadicLyapunov q n) / n) atTop
      (𝓝 ((-S.lyapunov) * (lowerHausdorffDimension (μ : Measure ℝ)).toReal)) := by
  have h := (S.translationEntropyIncrement_div_tendsto_zero μ hμ hdim hq).add
    (S.wordTranslationEntropy_coarse_div_tendsto μ hμ)
  convert h using 1
  · funext n
    dsimp [translationEntropyIncrement]
    ring
  · simp

theorem jointDyadicWordEntropy_fine_div_tendsto (S : System ι)
    (μ : ProbabilityMeasure ℝ) (hμ : S.IsStationary (μ : Measure ℝ))
    (hdim : (lowerHausdorffDimension (μ : Measure ℝ)).toReal < 1)
    {q : ℝ} (hq : 1 < q) :
    Tendsto (fun n : ℕ ↦ S.jointDyadicWordEntropy n
      (targetRatioLevel S.dyadicLyapunov q n) / n) atTop
      (𝓝 ((-S.lyapunov) * (lowerHausdorffDimension (μ : Measure ℝ)).toReal)) := by
  have h := (S.jointDyadicWordEntropy_increment_div_tendsto_zero μ hμ hdim hq).add
    (S.jointDyadicWordEntropy_coarse_div_tendsto μ hμ)
  convert h using 1
  · funext n
    ring
  · simp

end ExactOverlaps.SelfSimilar.System
