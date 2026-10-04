module

public import ExactOverlaps.SelfSimilar.HochmanTranslation
public import ExactOverlaps.SelfSimilar.JointWordConditionalEntropy

/-!
Hochman's Theorem 1.4 for finite systems of signed contracting real similarities.
The actual product word law retains both its translation and its signed ratio.
The real source scale is `n′ = κ n`; a real dyadic level denotes its floor.
Our Shannon entropy uses natural logarithms, so division by `log 2` gives
the paper's base-two entropy.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι]

theorem jointDyadicWordEntropy_increment_div_tendsto_zero (S : System ι)
    (μ : ProbabilityMeasure ℝ) (hμ : S.IsStationary (μ : Measure ℝ))
    (hdim : (lowerHausdorffDimension (μ : Measure ℝ)).toReal < 1)
    {q : ℝ} (hq : 1 < q) :
    Tendsto (fun n : ℕ ↦
      (S.jointDyadicWordEntropy n (targetRatioLevel S.dyadicLyapunov q n) -
        S.jointDyadicWordEntropy n (targetRatioLevel S.dyadicLyapunov 1 n)) / n)
      atTop (𝓝 0) := by
  have h := (S.joint_increment_error_div_tendsto_zero
    (targetRatioLevel S.dyadicLyapunov 1) (targetRatioLevel S.dyadicLyapunov q)).add
      (S.translationEntropyIncrement_div_tendsto_zero μ hμ hdim hq)
  convert h using 1
  · funext n
    dsimp [translationEntropyIncrement]
    ring
  · simp

theorem jointDyadicWordConditionalEntropy_div_tendsto_zero (S : System ι)
    (μ : ProbabilityMeasure ℝ) (hμ : S.IsStationary (μ : Measure ℝ))
    (hdim : (lowerHausdorffDimension (μ : Measure ℝ)).toReal < 1)
    {q : ℝ} (hq : 1 < q) :
    Tendsto (fun n : ℕ ↦
      S.jointDyadicWordConditionalEntropy n (targetRatioLevel S.dyadicLyapunov 1 n)
        (targetRatioLevel S.dyadicLyapunov q n) / n) atTop (𝓝 0) := by
  have heq (n : ℕ) := S.jointDyadicWordConditionalEntropy_eq_increment n
    (targetRatioLevel_mono S.dyadicLyapunov_pos.le hq.le n)
  simpa only [heq] using S.jointDyadicWordEntropy_increment_div_tendsto_zero μ hμ hdim hq

/-- Natural-logarithm entropy, with the source's exact real normalization `n′ = κ n`. -/
theorem jointDyadicWordConditionalEntropy_div_lyapunov_tendsto_zero (S : System ι)
    (μ : ProbabilityMeasure ℝ) (hμ : S.IsStationary (μ : Measure ℝ))
    (hdim : (lowerHausdorffDimension (μ : Measure ℝ)).toReal < 1)
    {q : ℝ} (hq : 1 < q) :
    Tendsto (fun n : ℕ ↦
      S.jointDyadicWordConditionalEntropy n (targetRatioLevel S.dyadicLyapunov 1 n)
        (targetRatioLevel S.dyadicLyapunov q n) / (S.dyadicLyapunov * n)) atTop (𝓝 0) := by
  have h := (S.jointDyadicWordConditionalEntropy_div_tendsto_zero μ hμ hdim hq).div_const
    S.dyadicLyapunov
  simpa only [div_div, mul_comm, zero_div] using h

/-- Hochman 2014, Theorem 1.4: the base-two conditional entropy of the fine
translation partition, retaining the exact signed ratio, is `o(n′)` whenever
the stationary measure has standard lower Hausdorff dimension less than one. -/
theorem hochman_theorem_1_4 (S : System ι)
    (μ : ProbabilityMeasure ℝ) (hμ : S.IsStationary (μ : Measure ℝ))
    (hdim : lowerHausdorffDimension (μ : Measure ℝ) < 1)
    {q : ℝ} (hq : 1 < q) :
    Tendsto (fun n : ℕ ↦
      (S.jointDyadicWordConditionalEntropy n (targetRatioLevel S.dyadicLyapunov 1 n)
        (targetRatioLevel S.dyadicLyapunov q n) / Real.log 2) /
          (S.dyadicLyapunov * n)) atTop (𝓝 0) := by
  have hd : (lowerHausdorffDimension (μ : Measure ℝ)).toReal < 1 := by
    have hfinite : lowerHausdorffDimension (μ : Measure ℝ) ≠ ⊤ :=
      ne_top_of_lt hdim
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal hfinite ENNReal.one_ne_top).mpr hdim
  have h := (S.jointDyadicWordConditionalEntropy_div_lyapunov_tendsto_zero μ hμ hd hq).div_const
    (Real.log 2)
  convert h using 1
  · funext n
    rw [div_div, div_div, mul_comm (Real.log 2)]
  · simp

end ExactOverlaps.SelfSimilar.System
