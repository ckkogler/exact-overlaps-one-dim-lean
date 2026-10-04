module

public import ExactOverlaps.SelfSimilar.BufferedEntropyApproximation
public import ExactOverlaps.SelfSimilar.EntropyIncrementComparison
public import ExactOverlaps.SelfSimilar.ContractionScaleComparison

/-!
The finite translation law and stationary measure have the same entropy per
letter at the Lyapunov scale, for arbitrary signed contraction factors.
This removes the positive buffer from the preceding coupling estimate. No
entropy-dimension limit or exact-dimensionality theorem is assumed here.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι]

/-- Coarse entropy approximation at the exact rounded Lyapunov scale. -/
theorem lyapunov_entropy_error_div_tendsto_zero (S : System ι) (ν : ProbabilityMeasure ℝ)
    (hν : S.IsStationary (ν : Measure ℝ)) :
    Tendsto (fun n : ℕ ↦
      (Entropy.dyadicEntropy ν (S.hasBoundedSupport hν)
          (contractionScale (Real.exp S.lyapunov) n) -
        Entropy.dyadicEntropy (S.wordTranslationProbability n)
          (S.wordTranslationProbability_hasBoundedSupport n)
          (contractionScale (Real.exp S.lyapunov) n)) / n) atTop (𝓝 0) := by
  let e (n : ℕ) (i : ℤ) : ℝ :=
    Entropy.dyadicEntropy ν (S.hasBoundedSupport hν) i -
      Entropy.dyadicEntropy (S.wordTranslationProbability n)
        (S.wordTranslationProbability_hasBoundedSupport n) i
  change Tendsto (fun n : ℕ ↦ e n (contractionScale (Real.exp S.lyapunov) n) / n)
    atTop (𝓝 0)
  rw [Metric.tendsto_nhds]
  intro τ hτ
  let ε := min (τ / 4) (-S.lyapunov / 2)
  have hε : 0 < ε := lt_min (by positivity) (div_pos (neg_pos.mpr S.lyapunov_neg) (by norm_num))
  have hετ : ε ≤ τ / 4 := min_le_left _ _
  have hεχ : ε ≤ -S.lyapunov / 2 := min_le_right _ _
  have hεupper : S.lyapunov + ε ≤ 0 := by have := S.lyapunov_neg; linarith
  have hbuf := S.buffered_entropy_error_div_tendsto_zero ν hν hε hεupper
  change Tendsto (fun n : ℕ ↦ e n (contractionScale (Real.exp (S.lyapunov + ε)) n) / n)
    atTop (𝓝 0) at hbuf
  have hlog := tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)
  have hB : ∀ᶠ n : ℕ in atTop,
      |e n (contractionScale (Real.exp (S.lyapunov + ε)) n) / n| < τ / 4 := by
    simpa only [Real.dist_eq, sub_zero] using
      (Metric.tendsto_nhds.mp hbuf) (τ / 4) (by positivity)
  have hL : ∀ᶠ n : ℕ in atTop, |Real.log 2 / n| < τ / 4 := by
    simpa only [Real.dist_eq, sub_zero] using
      (Metric.tendsto_nhds.mp hlog) (τ / 4) (by positivity)
  filter_upwards [hB, hL, eventually_gt_atTop 0] with n hBn hLn hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let i := contractionScale (Real.exp (S.lyapunov + ε)) n
  let j := contractionScale (Real.exp S.lyapunov) n
  have hij : i ≤ j := contractionScale_exp_add_le S.lyapunov hε.le n
  have hgap : ((j - i : ℤ) : ℝ) * Real.log 2 ≤ (n : ℝ) * ε + Real.log 2 :=
    contractionScale_exp_gap_le S.lyapunov ε n
  have hc := Entropy.abs_entropy_difference_le_at_lower_scale ν
    (S.wordTranslationProbability n) (S.hasBoundedSupport hν)
    (S.wordTranslationProbability_hasBoundedSupport n) hij
  have hc' : |e n j| ≤ |e n i| + (n : ℝ) * ε + Real.log 2 := by
    change |e n j| ≤ |e n i| + ((j - i : ℤ) : ℝ) * Real.log 2 at hc
    linarith
  have hd := div_le_div_of_nonneg_right hc' hn'.le
  have he : (|e n i| + (n : ℝ) * ε + Real.log 2) / n =
      |e n i| / n + ε + Real.log 2 / n := by field_simp
  rw [he] at hd
  have hBi : |e n i| / n < τ / 4 := by
    simpa only [abs_div, abs_of_pos hn'] using hBn
  have hLi : Real.log 2 / n < τ / 4 := (le_abs_self _).trans_lt hLn
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hn']
  change |e n j| / n < τ
  linarith

end ExactOverlaps.SelfSimilar.System
