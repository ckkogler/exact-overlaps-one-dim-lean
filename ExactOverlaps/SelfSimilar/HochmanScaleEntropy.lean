module

public import ExactOverlaps.SelfSimilar.HochmanFineEntropy
public import ExactOverlaps.SelfSimilar.ScaleEntropyComparison

/-!
Hochman's entropy estimate at the actual translation-averaged exponential
scales used in Lemma 3.2 of the exact-overlaps paper. Entropy uses natural
logarithms, and the Lyapunov exponent is that of the given product word law.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ExactOverlaps.SelfSimilar.System

open Entropy
variable {ι : Type*} [Fintype ι]

theorem ratioLevel_exponential_scale (S : System ι) {C : ℝ} (hC : 0 < C) (n : ℕ) :
    ratioLevel (C ^ (-(n : ℤ))) =
      targetRatioLevel S.dyadicLyapunov (Real.log C / (-S.lyapunov)) n := by
  unfold ratioLevel targetRatioLevel dyadicLyapunov
  rw [abs_of_pos (zpow_pos hC _), Real.log_zpow]
  congr 1
  push_cast
  have hχ : S.lyapunov ≠ 0 := S.lyapunov_neg.ne
  field_simp [hχ]

theorem wordTranslation_scale_entropy_div_tendsto (S : System ι)
    (μ : ProbabilityMeasure ℝ) (hμ : S.IsStationary (μ : Measure ℝ))
    (hdim : (lowerHausdorffDimension (μ : Measure ℝ)).toReal < 1)
    {C : ℝ} (hC : Real.exp (-S.lyapunov) < C) :
    Tendsto (fun n : ℕ ↦ ScaleEntropy.entropy (S.wordTranslationProbability n)
      (S.wordTranslationProbability_hasBoundedSupport n) (C ^ (-(n : ℤ)))
      (zpow_pos ((Real.exp_pos _).trans hC) _) / n) atTop
      (𝓝 ((-S.lyapunov) * (lowerHausdorffDimension (μ : Measure ℝ)).toReal)) := by
  have hCpos : 0 < C := (Real.exp_pos _).trans hC
  have hq : 1 < Real.log C / (-S.lyapunov) := by
    apply (lt_div_iff₀ (neg_pos.mpr S.lyapunov_neg)).mpr
    have h := Real.log_lt_log (Real.exp_pos (-S.lyapunov)) hC
    simpa only [Real.log_exp, one_mul] using h
  have hf := S.wordTranslationEntropy_fine_div_tendsto μ hμ hdim hq
  have he : Tendsto (fun n : ℕ ↦
      (ScaleEntropy.entropy (S.wordTranslationProbability n)
          (S.wordTranslationProbability_hasBoundedSupport n) (C ^ (-(n : ℤ)))
          (zpow_pos hCpos _) -
        dyadicEntropy (S.wordTranslationProbability n)
          (S.wordTranslationProbability_hasBoundedSupport n)
          (targetRatioLevel S.dyadicLyapunov (Real.log C / (-S.lyapunov)) n)) / n)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n ↦ ?_) (tendsto_const_div_atTop_nhds_zero_nat (Real.log 7))
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    simpa only [S.ratioLevel_exponential_scale hCpos] using
      ScaleEntropy.abs_entropy_sub_ratioLevel_entropy_le (S.wordTranslationProbability n)
        (S.wordTranslationProbability_hasBoundedSupport n) (C ^ (-(n : ℤ))) (zpow_pos hCpos _)
  convert he.add hf using 1
  · funext n
    ring
  · simp

/-- Lemma 3.2: for every `C > exp |χ|`, the genuine averaged mesh entropy of
the random word translation, divided by the word length, tends to `|χ| dim μ`. -/
theorem hochman_scale_entropy (S : System ι)
    (μ : ProbabilityMeasure ℝ) (hμ : S.IsStationary (μ : Measure ℝ))
    (hdim : lowerHausdorffDimension (μ : Measure ℝ) < 1)
    {C : ℝ} (hC : Real.exp |S.lyapunov| < C) :
    Tendsto (fun n : ℕ ↦ ScaleEntropy.entropy (S.wordTranslationProbability n)
      (S.wordTranslationProbability_hasBoundedSupport n) (C ^ (-(n : ℤ)))
      (zpow_pos ((Real.exp_pos _).trans hC) _) / n) atTop
      (𝓝 (|S.lyapunov| * (lowerHausdorffDimension (μ : Measure ℝ)).toReal)) := by
  have hd : (lowerHausdorffDimension (μ : Measure ℝ)).toReal < 1 := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal (ne_top_of_lt hdim) ENNReal.one_ne_top).mpr hdim
  have hC' : Real.exp (-S.lyapunov) < C := by
    simpa only [abs_of_neg S.lyapunov_neg] using hC
  simpa only [abs_of_neg S.lyapunov_neg] using
    S.wordTranslation_scale_entropy_div_tendsto μ hμ hd hC'

/-- The equivalent `n |χ| dim μ + o(n)` formulation of Lemma 3.2. -/
theorem hochman_scale_entropy_isLittleO (S : System ι)
    (μ : ProbabilityMeasure ℝ) (hμ : S.IsStationary (μ : Measure ℝ))
    (hdim : lowerHausdorffDimension (μ : Measure ℝ) < 1)
    {C : ℝ} (hC : Real.exp |S.lyapunov| < C) :
    Asymptotics.IsLittleO atTop (fun n : ℕ ↦
      ScaleEntropy.entropy (S.wordTranslationProbability n)
        (S.wordTranslationProbability_hasBoundedSupport n) (C ^ (-(n : ℤ)))
        (zpow_pos ((Real.exp_pos _).trans hC) _) -
          n * |S.lyapunov| * (lowerHausdorffDimension (μ : Measure ℝ)).toReal)
      (fun n : ℕ ↦ (n : ℝ)) := by
  apply (Asymptotics.isLittleO_iff_tendsto' ?_).mpr
  · have h := (S.hochman_scale_entropy μ hμ hdim hC).sub_const
      (|S.lyapunov| * (lowerHausdorffDimension (μ : Measure ℝ)).toReal)
    simp only [sub_self] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    field_simp [hn']
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact fun hzero ↦ False.elim ((Nat.cast_ne_zero.mpr hn.ne') hzero)

end ExactOverlaps.SelfSimilar.System
