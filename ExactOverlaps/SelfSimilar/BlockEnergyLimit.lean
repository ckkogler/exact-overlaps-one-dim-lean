module

public import ExactOverlaps.SelfSimilar.BlockParameterChoice
public import ExactOverlaps.SelfSimilar.BlockCountLimits
public import ExactOverlaps.SelfSimilar.RandomWalkTranslationEntropy
public import ExactOverlaps.SelfSimilar.HochmanScaleEntropy

/-! The limiting slope of the genuine finite-block energy lower bound. -/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ExactOverlaps.SelfSimilar.System

open Entropy
variable {ι : Type*} [Fintype ι]

noncomputable def blockEnergyLower (S : System ι) (N m : ℕ) (C : ℝ) (hC : 0 < C) (n : ℕ) : ℝ :=
  1 / (30 * m) *
    (finiteEntropy (S.wordTranslationLaw n) (S.wordTranslationLaw_support_finite n) -
      ScaleEntropy.entropy (S.wordTranslationProbability n)
        (S.wordTranslationProbability_hasBoundedSupport n) (C ^ (-(n : ℤ))) (zpow_pos hC _) -
      ((n / N : ℕ) + 1 : ℝ) * S.blockEntropyPenalty N m) - 1 / 2

theorem blockEnergyLower_le (S : System ι) {N : ℕ} (hN : 0 < N)
    (m : ℕ) (hm : 0 < m) (C : ℝ) (hC : 0 < C) (n : ℕ) :
    S.blockEnergyLower N m C hC n ≤ S.meanRatioTranslationEnergy n (C ^ (-(n : ℤ))) :=
  S.word_block_energy_bound_all hN n m hm (zpow_pos hC _)

theorem blockEnergyLower_div_tendsto (S : System ι)
    (μ : ProbabilityMeasure ℝ) (hμ : S.IsStationary (μ : Measure ℝ))
    (hdim : (lowerHausdorffDimension (μ : Measure ℝ)).toReal < 1)
    {N : ℕ} (hN : 0 < N) (m : ℕ) {C : ℝ} (hC : Real.exp |S.lyapunov| < C) :
    Tendsto (fun n : ℕ ↦ S.blockEnergyLower N m C ((Real.exp_pos _).trans hC) n / n)
      atTop (𝓝 ((S.randomWalkEntropyRate -
        |S.lyapunov| * (lowerHausdorffDimension (μ : Measure ℝ)).toReal -
          S.blockEntropyPenalty N m / N) / (30 * m))) := by
  have hE := S.wordTranslation_scale_entropy_div_tendsto μ hμ hdim
    (show Real.exp (-S.lyapunov) < C by simpa only [abs_of_neg S.lyapunov_neg] using hC)
  have h := (((S.wordTranslationLaw_entropy_div_tendsto_rate.sub hE).sub
    ((block_count_div_tendsto hN).mul_const (S.blockEntropyPenalty N m))).const_mul
      (1 / (30 * (m : ℝ)))).sub (tendsto_const_div_atTop_nhds_zero_nat (1 / 2 : ℝ))
  convert h using 1
  · funext n
    dsimp [blockEnergyLower]
    ring
  · simp only [sub_zero, abs_of_neg S.lyapunov_neg]
    congr 1
    ring

end ExactOverlaps.SelfSimilar.System
