module

public import ExactOverlaps.SelfSimilar.BufferedEntropyBound
public import ExactOverlaps.SelfSimilar.EntropyBufferChoice

/-!
The explicit entropy upper bound has a computable limit once the genuine
stationary-tail entropy residual is supplied. Every remaining error term
has already been proved negligible.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ExactOverlaps.SelfSimilar.System

open Entropy
variable {ι : Type*} [Fintype ι]

theorem bufferedEntropyUpper_div_tendsto (S : System ι)
    (μ : ProbabilityMeasure ℝ) (hμ : S.IsStationary (μ : Measure ℝ))
    (e γ ε q : ℝ) (hγ : 0 < γ) (hε : 0 < ε)
    (hres : Tendsto (fun n : ℕ ↦
      S.stationaryTailEntropyResidual μ hμ n (bufferedRatioLevel S.dyadicLyapunov ε n)
        (targetRatioLevel S.dyadicLyapunov q n) / n) atTop
      (𝓝 (2 * (lowerHausdorffDimension (μ : Measure ℝ)).toReal * ε * Real.log 2))) :
    Tendsto (fun n : ℕ ↦ S.bufferedEntropyUpper μ hμ e γ ε q n / n) atTop
      (𝓝 (bufferedEntropyLimit (lowerHausdorffDimension (μ : Measure ℝ)).toReal
        S.dyadicLyapunov e γ ε q)) := by
  let i := bufferedRatioLevel S.dyadicLyapunov ε
  let f := targetRatioLevel S.dyadicLyapunov q
  let B : ℕ → ℝ := fun n ↦ S.ratioClassBadMass n (S.typicalRatioClasses ε n)
  let D : ℕ → ℝ := fun n ↦ ((f n - i n : ℤ) : ℝ)
  have hB : Tendsto B atTop (𝓝 0) := S.typicalRatioClasses_badMass_tendsto_zero hε
  have hD : Tendsto (fun n : ℕ ↦ D n / n) atTop (𝓝 ((q - 1) * S.dyadicLyapunov + 2 * ε)) := by
    have h := (targetRatioLevel_div_tendsto S.dyadicLyapunov q).sub
      (bufferedRatioLevel_div_tendsto S.dyadicLyapunov ε)
    convert h using 1
    · funext n
      simp only [D, f, i, Int.cast_sub, sub_div]
    · ring_nf
  have heconst : Tendsto (fun _ : ℕ ↦ e) atTop (𝓝 e) := tendsto_const_nhds
  have hmain := ((heconst.add hB).mul hD).mul_const (Real.log 2)
  have hres' := (hres.add (tendsto_const_div_atTop_nhds_zero_nat (2 * Real.log 2))).div_const γ
  have hεconst : Tendsto (fun _ : ℕ ↦ 3 * ε) atTop (𝓝 (3 * ε)) := tendsto_const_nhds
  have hgap := ((hεconst.add (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))).add
    (hD.mul hB)).mul_const (Real.log 2)
  have hseq := ((S.wordRatioLaw_entropy_div_tendsto_zero.add hmain).add hres').add hgap
  have hlim : Tendsto (fun n : ℕ ↦
      finiteEntropy (S.wordRatioLaw n) (S.wordRatioLaw_support_finite n) / n +
        (e + B n) * (D n / n) * Real.log 2 +
        (S.stationaryTailEntropyResidual μ hμ n (i n) (f n) / n + (2 * Real.log 2) / n) / γ +
        (3 * ε + 1 / n + D n / n * B n) * Real.log 2) atTop
      (𝓝 (bufferedEntropyLimit (lowerHausdorffDimension (μ : Measure ℝ)).toReal
        S.dyadicLyapunov e γ ε q)) := by
    simpa only [add_zero, zero_add, mul_zero, bufferedEntropyLimit] using hseq
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  dsimp [bufferedEntropyUpper, B, D, i, f]
  field_simp [hn', hγ.ne']

end ExactOverlaps.SelfSimilar.System
