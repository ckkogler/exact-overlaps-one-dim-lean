module

public import ExactOverlaps.SelfSimilar.AffineEntropy
public import ExactOverlaps.Entropy.DyadicDilation
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
Uniform entropy lower bounds for affine copies whose rescaled ratios stay
away from zero. The translation and sign are arbitrary. The sole limiting
input is the proved global entropy limit of the original probability.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace ExactOverlaps

noncomputable def RealSimilarity.dyadicScale (g : RealSimilarity) (k : ℤ) : RealSimilarity where
  ratio := (2 : ℝ) ^ k * g.ratio
  ratio_ne_zero := mul_ne_zero (zpow_ne_zero _ (by norm_num)) g.ratio_ne_zero
  shift := (2 : ℝ) ^ k * g.shift

theorem RealSimilarity.probability_map_dyadicScale (g : RealSimilarity)
    (μ : ProbabilityMeasure ℝ) (k : ℤ) :
    μ.map (g.dyadicScale k) = (μ.map g).map (Entropy.componentRescale k 0) := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (Entropy.measurable_componentRescale k 0) g.measurable]
  congr 1
  funext x
  simp only [RealSimilarity.dyadicScale, Entropy.componentRescale, Int.cast_zero,
    sub_zero, Function.comp_def]
  ring

namespace Entropy

theorem dyadicEntropy_affine_scale (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ)
    (g : RealSimilarity) (k i : ℤ) :
    dyadicEntropy (μ.map (g.dyadicScale k)) ((g.dyadicScale k).hasBoundedSupport_map μ hμ) i =
      dyadicEntropy (μ.map g) (g.hasBoundedSupport_map μ hμ) (k + i) := by
  simpa only [← g.probability_map_dyadicScale μ k] using
    dyadicEntropy_dilate (μ.map g) (g.hasBoundedSupport_map μ hμ) k i

theorem uniform_affine_entropy_lower_bound (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) {d a : ℝ}
    (hlim : Tendsto (normalizedDyadicEntropy μ hμ) atTop (𝓝 d)) (ha : 0 < a)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → 0 < m → ∀ k : ℕ, ∀ g : RealSimilarity,
      a ≤ (2 : ℝ) ^ k * |g.ratio| →
      (d - δ) * ((m : ℝ) * Real.log 2) ≤
        dyadicEntropy (μ.map g) (g.hasBoundedSupport_map μ hμ) ((k : ℤ) + m) := by
  obtain ⟨K, hK⟩ := exists_nat_ge a⁻¹
  let C : ℝ := Real.log (2 * K + 3 : ℝ)
  have herror : Tendsto (fun m : ℕ ↦ C / ((m : ℝ) * Real.log 2)) atTop (𝓝 0) := by
    have h := tendsto_const_div_atTop_nhds_zero_nat (C / Real.log 2)
    have he : (fun m : ℕ ↦ C / ((m : ℝ) * Real.log 2)) =
        (fun m : ℕ ↦ (C / Real.log 2) / m) := by funext m; ring
    rw [he]
    exact h
  have hnear : ∀ᶠ m : ℕ in atTop,
      d - δ < normalizedDyadicEntropy μ hμ m - C / ((m : ℝ) * Real.log 2) := by
    have h := hlim.sub herror
    simp only [sub_zero] at h
    exact h.eventually (lt_mem_nhds (by linarith))
  obtain ⟨M, hM⟩ := eventually_atTop.mp hnear
  refine ⟨M, fun m hm hmpos k g hratio ↦ ?_⟩
  have hden : 0 < (m : ℝ) * Real.log 2 :=
    mul_pos (Nat.cast_pos.mpr hmpos) (Real.log_pos (by norm_num))
  have hscale : |(g.dyadicScale k).ratio| = (2 : ℝ) ^ k * |g.ratio| := by
    simp only [RealSimilarity.dyadicScale, abs_mul, zpow_natCast,
      abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) k)]
  have hinv : |(g.dyadicScale k).ratio|⁻¹ ≤ K := by
    rw [hscale]
    exact (inv_anti₀ ha hratio).trans hK
  have hb := dyadicEntropy_le_map_affine_add μ hμ (g.dyadicScale k) hinv m
  rw [dyadicEntropy_affine_scale μ hμ g k m] at hb
  have hn := (hM m hm).le
  rw [normalizedDyadicEntropy, ← sub_div] at hn
  have hh := (le_div_iff₀ hden).mp hn
  dsimp [C] at hh
  linarith

end Entropy
end ExactOverlaps
