module

public import ExactOverlaps.SelfSimilar.RatioTailTypical
public import ExactOverlaps.SelfSimilar.RatioTailAverageError
public import ExactOverlaps.SelfSimilar.EntropyLevelLimits

/-!
The exact averaged entropy of the scaled stationary tails at a fixed
super-Lyapunov scale. Atypical contraction classes are controlled by their
vanishing true probability and a common linear entropy bound.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ExactOverlaps.SelfSimilar.System

open Entropy
variable {ι : Type*} [Fintype ι]

theorem averageRatioScaledEntropy_target_div_tendsto (S : System ι)
    (μ : ProbabilityMeasure ℝ) (hμ : S.IsStationary (μ : Measure ℝ))
    {q : ℝ} (hq : 1 < q) :
    Tendsto (fun n : ℕ ↦ S.averageRatioScaledEntropy μ (S.hasBoundedSupport hμ) n
      (targetRatioLevel S.dyadicLyapunov q n) / n) atTop
      (𝓝 ((lowerHausdorffDimension (μ : Measure ℝ)).toReal *
        ((q - 1) * S.dyadicLyapunov) * Real.log 2)) := by
  let d := (lowerHausdorffDimension (μ : Measure ℝ)).toReal
  let T := d * ((q - 1) * S.dyadicLyapunov) * Real.log 2
  let f := targetRatioLevel S.dyadicLyapunov q
  have hlim := S.normalizedDyadicEntropy_tendsto_dimension μ hμ
  have hglobal := S.dyadicEntropy_level_div_tendsto_dimension μ hμ
    (mul_pos (show 0 < q by linarith) S.dyadicLyapunov_pos)
    (targetRatioLevel_div_tendsto S.dyadicLyapunov q)
  rw [Metric.tendsto_nhds]
  intro τ hτ
  obtain ⟨η, hη, htypical⟩ := S.ratioScaledEntropy_target_uniform_on_typical μ
    (S.hasBoundedSupport hμ) hlim ENNReal.toReal_nonneg hq (half_pos hτ)
  have hbad := S.wordRatioLaw_atypical_level_mass_tendsto_zero hη
  let B (n : ℕ) := dyadicEntropy μ (S.hasBoundedSupport hμ) (f n) / n + Real.log 5 / n + |T|
  have herror : Tendsto (fun n : ℕ ↦ B n *
      ((S.wordRatioLaw n).toMeasure (S.atypicalRatioLevelSet η n)).toReal) atTop (𝓝 0) := by
    simpa only [add_zero, mul_zero] using
      ((hglobal.add (tendsto_const_div_atTop_nhds_zero_nat (Real.log 5))).add_const |T|).mul hbad
  have hsmall : ∀ᶠ n : ℕ in atTop, B n *
      ((S.wordRatioLaw n).toMeasure (S.atypicalRatioLevelSet η n)).toReal < τ / 2 :=
    herror.eventually (gt_mem_nhds (half_pos hτ))
  filter_upwards [htypical, hsmall] with n hn herr
  have hb := S.averageRatioScaledEntropy_error_le_split μ (S.hasBoundedSupport hμ)
    n (f n) T (S.atypicalRatioLevelSet η n) (S.measurableSet_atypicalRatioLevelSet η n)
    (C := τ / 2) (B := B n) (half_pos hτ).le
    (fun r hr ↦ by
      have ht : (S.dyadicLyapunov - η) * n ≤ (ratioLevel r : ℝ) ∧
          (ratioLevel r : ℝ) ≤ (S.dyadicLyapunov + η) * n := by
        simpa only [atypicalRatioLevelSet, Set.mem_ofPred_eq, not_not] using hr
      exact hn r ht.1 ht.2)
    (fun r ↦ by
      have hnonneg := div_nonneg (dyadicEntropy_nonneg (S.ratioScaledProbability μ n r)
        (S.ratioScaledProbability_hasBoundedSupport μ (S.hasBoundedSupport hμ) n r) (f n))
        (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      have hu := div_le_div_of_nonneg_right
        (S.ratioScaledEntropy_le μ (S.hasBoundedSupport hμ) n r (f n))
        (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      have ha := abs_sub_le (dyadicEntropy (S.ratioScaledProbability μ n r)
        (S.ratioScaledProbability_hasBoundedSupport μ (S.hasBoundedSupport hμ) n r) (f n) / n) 0 T
      simp only [sub_zero, zero_sub, abs_neg, abs_of_nonneg hnonneg, add_div] at ha hu
      dsimp [B]
      linarith)
  rw [Real.dist_eq]
  change |S.averageRatioScaledEntropy μ (S.hasBoundedSupport hμ) n (f n) / n - T| < τ
  linarith

end ExactOverlaps.SelfSimilar.System
