module

public import ExactOverlaps.SelfSimilar.BufferedEntropyBound
public import ExactOverlaps.SelfSimilar.RatioTailEntropy
public import ExactOverlaps.SelfSimilar.RatioTailFineEntropy

/-! The stationary-versus-tail residual at a common buffered coarse scale. -/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ExactOverlaps.SelfSimilar.System

open Entropy
variable {ι : Type*} [Fintype ι]

theorem stationaryTailEntropyResidual_div_tendsto (S : System ι)
    (μ : ProbabilityMeasure ℝ) (hμ : S.IsStationary (μ : Measure ℝ))
    {ε q : ℝ} (hε : 0 < ε) (hεsmall : 2 * ε < S.dyadicLyapunov) (hq : 1 < q) :
    Tendsto (fun n : ℕ ↦
      S.stationaryTailEntropyResidual μ hμ n (bufferedRatioLevel S.dyadicLyapunov ε n)
        (targetRatioLevel S.dyadicLyapunov q n) / n) atTop
      (𝓝 (2 * (lowerHausdorffDimension (μ : Measure ℝ)).toReal * ε * Real.log 2)) := by
  have hf := S.dyadicEntropy_level_div_tendsto_dimension μ hμ
    (mul_pos (show 0 < q by linarith) S.dyadicLyapunov_pos)
    (targetRatioLevel_div_tendsto S.dyadicLyapunov q)
  have hi := S.dyadicEntropy_level_div_tendsto_dimension μ hμ (sub_pos.mpr hεsmall)
    (bufferedRatioLevel_div_tendsto S.dyadicLyapunov ε)
  have htf := S.averageRatioScaledEntropy_target_div_tendsto μ hμ hq
  have hti := S.averageRatioScaledEntropy_buffered_div_tendsto_zero μ hμ hε hεsmall
  convert ((hf.sub hi).sub htf).add hti using 1
  · funext n
    simp only [stationaryTailEntropyResidual, sub_div, add_div]
  · ring_nf

end ExactOverlaps.SelfSimilar.System
