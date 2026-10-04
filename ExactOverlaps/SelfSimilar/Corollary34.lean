module

public import ExactOverlaps.SelfSimilar.BlockEnergyLimit

/-! Corollary 3.4: a linear supply of conditional variance energy below exponential scales. -/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι]

/-- The positive energy slope is chosen before the exponential scale `C`.
The dimension is the standard lower Hausdorff dimension of the actual stationary
probability, and the random-walk entropy rate is the proved Fekete limit. -/
theorem corollary_3_4 (S : System ι)
    (μ : ProbabilityMeasure ℝ) (hμ : S.IsStationary (μ : Measure ℝ))
    (hdim : (lowerHausdorffDimension (μ : Measure ℝ)).toReal <
      min 1 (S.randomWalkEntropyRate / |S.lyapunov|)) :
    ∃ η : ℝ, 0 < η ∧ ∀ C : ℝ, Real.exp |S.lyapunov| < C →
      ∀ᶠ n : ℕ in atTop, η * n ≤ S.meanRatioTranslationEnergy n (C ^ (-(n : ℤ))) := by
  let d := (lowerHausdorffDimension (μ : Measure ℝ)).toReal
  let δ := S.randomWalkEntropyRate - |S.lyapunov| * d
  have hχ : 0 < |S.lyapunov| := abs_pos.mpr S.lyapunov_neg.ne
  have hδ : 0 < δ := by
    have h := (lt_div_iff₀ hχ).mp (lt_min_iff.mp hdim).2
    dsimp [δ, d]
    nlinarith
  obtain ⟨N, hN, m, hm, hpen⟩ := S.exists_small_blockEntropyPenalty (half_pos hδ)
  let ℓ := (δ - S.blockEntropyPenalty N m / N) / (30 * m)
  have hmreal : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hℓ : 0 < ℓ := div_pos (by linarith) (by positivity)
  refine ⟨ℓ / 2, half_pos hℓ, ?_⟩
  intro C hC
  have hlim := S.blockEnergyLower_div_tendsto μ hμ (lt_min_iff.mp hdim).1 hN m hC
  change Tendsto (fun n : ℕ ↦ S.blockEnergyLower N m C ((Real.exp_pos _).trans hC) n / n)
    atTop (𝓝 ℓ) at hlim
  have hsmall := hlim.eventually (lt_mem_nhds (half_lt_self hℓ))
  filter_upwards [hsmall, eventually_gt_atTop 0] with n hn hnpos
  have hnreal : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
  have hb := div_le_div_of_nonneg_right
    (S.blockEnergyLower_le hN m hm C ((Real.exp_pos _).trans hC) n) hnreal.le
  exact (le_div_iff₀ hnreal).mp (hn.le.trans hb)

end ExactOverlaps.SelfSimilar.System
