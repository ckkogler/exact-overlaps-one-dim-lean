module

public import ExactOverlaps.SelfSimilar.AffineEntropy
public import ExactOverlaps.SelfSimilar.UniformEntropyDimension

/-!
Uniform upper bounds for the level-averaged component entropy of affine
images with bounded ratio. Translation is unrestricted, including shifts
that move atoms across dyadic boundaries.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace ExactOverlaps.Entropy

theorem levelAverageComponentEntropy_affine_le (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (g : RealSimilarity) {K n m : ℕ}
    (hK : |g.ratio| ≤ K) (hn : 0 < n) (hm : 0 < m) :
    levelAverageComponentEntropy (μ.map g) (g.hasBoundedSupport_map μ hμ) n m ≤
      normalizedDyadicEntropy μ hμ n + (m : ℝ) / n +
        (dyadicEntropy μ hμ 0 + 2 * Real.log (2 * K + 3 : ℝ)) / ((n : ℝ) * Real.log 2) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hden : 0 < (n : ℝ) * Real.log 2 := mul_pos hn' (Real.log_pos (by norm_num))
  have hav := (abs_le.mp (abs_levelAverageComponentEntropy_sub_le
    (μ.map g) (g.hasBoundedSupport_map μ hμ) hn hm)).2
  have hfin := div_le_div_of_nonneg_right (dyadicEntropy_map_affine_sub_le μ hμ g hK n) hden.le
  have hzero := div_le_div_of_nonneg_right (dyadicEntropy_map_affine_sub_le μ hμ g hK 0) hden.le
  simp only [sub_div] at hfin hzero
  unfold normalizedDyadicEntropy at hav ⊢
  rw [add_div, mul_div_assoc]
  linarith

theorem eventually_uniform_affine_mean_lt (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) {d : ℝ}
    (hlim : Tendsto (normalizedDyadicEntropy μ hμ) atTop (𝓝 d))
    (K : ℕ) {m : ℕ} (hm : 0 < m) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ g : RealSimilarity, |g.ratio| ≤ K →
      levelAverageComponentEntropy (μ.map g) (g.hasBoundedSupport_map μ hμ) n m < d + δ := by
  let C : ℝ := dyadicEntropy μ hμ 0 + 2 * Real.log (2 * K + 3 : ℝ)
  have herr : Tendsto (fun n : ℕ ↦ C / ((n : ℝ) * Real.log 2)) atTop (𝓝 0) := by
    have h := tendsto_const_div_atTop_nhds_zero_nat (C / Real.log 2)
    convert h using 1
    funext n
    ring
  have hu : Tendsto (fun n : ℕ ↦ normalizedDyadicEntropy μ hμ n + (m : ℝ) / n +
      C / ((n : ℝ) * Real.log 2)) atTop (𝓝 d) := by
    simpa only [add_zero] using
      (hlim.add (tendsto_const_div_atTop_nhds_zero_nat (m : ℝ))).add herr
  filter_upwards [eventually_gt_atTop 0, hu.eventually (gt_mem_nhds (by linarith : d < d + δ))]
    with n hn hu'
  intro g hg
  exact (levelAverageComponentEntropy_affine_le μ hμ g hg hn hm).trans_lt hu'

end ExactOverlaps.Entropy
