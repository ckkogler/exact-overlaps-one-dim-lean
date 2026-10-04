module

public import ExactOverlaps.SelfSimilar.AffineConvolution
public import ExactOverlaps.SelfSimilar.AffineEntropyScale

/-!
The ordinary entropy-dimension limit holds uniformly over affine maps with
absolute ratios in a compact positive interval. Both orientations and all
translations are included, with the same eventual scale threshold.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace ExactOverlaps.Entropy

theorem uniform_affine_normalized_entropy_limit (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) {d a : ℝ}
    (hlim : Tendsto (normalizedDyadicEntropy μ hμ) atTop (𝓝 d)) (ha : 0 < a)
    (K : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ g : RealSimilarity, a ≤ |g.ratio| → |g.ratio| ≤ K →
      |normalizedDyadicEntropy (μ.map g) (g.hasBoundedSupport_map μ hμ) n - d| < δ := by
  obtain ⟨L, hL⟩ := exists_nat_ge (max a⁻¹ (K : ℝ))
  let C : ℝ := Real.log (2 * L + 3 : ℝ)
  have herror : Tendsto (fun n : ℕ ↦ C / ((n : ℝ) * Real.log 2)) atTop (𝓝 0) := by
    have h := tendsto_const_div_atTop_nhds_zero_nat (C / Real.log 2)
    convert h using 1
    funext n
    ring
  have hnear : ∀ᶠ n : ℕ in atTop, |normalizedDyadicEntropy μ hμ n - d| < δ / 2 := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp hlim) (δ / 2) (half_pos hδ)
  filter_upwards [hnear, herror.eventually (gt_mem_nhds (half_pos hδ))] with n hn herr
  intro g hga hgK
  have hforward : |g.ratio| ≤ L := hgK.trans ((le_max_right _ _).trans hL)
  have hinverse : |g.ratio|⁻¹ ≤ L := (inv_anti₀ ha hga).trans ((le_max_left _ _).trans hL)
  have hupper := normalizedDyadicEntropy_affine_le μ hμ g hforward n
  have hlower := normalizedDyadicEntropy_le_affine_add μ hμ g hinverse n
  change _ ≤ _ + C / ((n : ℝ) * Real.log 2) at hupper hlower
  rw [abs_lt] at hn ⊢
  constructor <;> linarith

theorem uniform_affine_fine_entropy_limit (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) {d a : ℝ}
    (hlim : Tendsto (normalizedDyadicEntropy μ hμ) atTop (𝓝 d)) (ha : 0 < a)
    (K : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → 0 < m → ∀ j : ℤ, ∀ g : RealSimilarity,
      a ≤ (2 : ℝ) ^ j * |g.ratio| → (2 : ℝ) ^ j * |g.ratio| ≤ K →
      |dyadicEntropy (μ.map g) (g.hasBoundedSupport_map μ hμ) (j + m) -
        d * ((m : ℝ) * Real.log 2)| < δ * ((m : ℝ) * Real.log 2) := by
  obtain ⟨M, hM⟩ := eventually_atTop.mp (uniform_affine_normalized_entropy_limit μ hμ hlim ha K hδ)
  refine ⟨M, fun m hm hmpos j g hglo hghi ↦ ?_⟩
  have hscale : |(g.dyadicScale j).ratio| = (2 : ℝ) ^ j * |g.ratio| := by
    simp only [RealSimilarity.dyadicScale, abs_mul,
      abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) j)]
  have h := hM m hm (g.dyadicScale j) (by simpa only [hscale] using hglo)
    (by simpa only [hscale] using hghi)
  simp only [normalizedDyadicEntropy, dyadicEntropy_affine_scale μ hμ g j m] at h
  have hden : 0 < (m : ℝ) * Real.log 2 :=
    mul_pos (Nat.cast_pos.mpr hmpos) (Real.log_pos (by norm_num))
  have he : dyadicEntropy (μ.map g) (g.hasBoundedSupport_map μ hμ) (j + m) /
      ((m : ℝ) * Real.log 2) - d =
      (dyadicEntropy (μ.map g) (g.hasBoundedSupport_map μ hμ) (j + m) -
        d * ((m : ℝ) * Real.log 2)) / ((m : ℝ) * Real.log 2) := by field_simp
  rw [he, abs_div, abs_of_pos hden] at h
  exact (div_lt_iff₀ hden).mp h

end ExactOverlaps.Entropy
