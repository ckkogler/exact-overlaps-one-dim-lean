module

public import ExactOverlaps.SelfSimilar.AffineEntropy
public import ExactOverlaps.Entropy.RealConvolution

/-! Actual affine pushforwards commute with convolution when their linear parts agree. -/

@[expose] public section

open MeasureTheory

namespace ExactOverlaps.RealSimilarity

theorem probability_map_comp (g h : RealSimilarity) (μ : ProbabilityMeasure ℝ) :
    μ.map (g.comp h) = (μ.map h).map g := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map g.measurable h.measurable]
  congr 1
  funext x
  exact g.comp_apply h x

end ExactOverlaps.RealSimilarity

namespace ExactOverlaps.Entropy

theorem realConvolution_map_affine (μ ν : ProbabilityMeasure ℝ)
    (g h q : RealSimilarity) (hr : g.ratio = q.ratio) (hs : h.ratio = q.ratio)
    (hb : g.shift + h.shift = q.shift) :
    realConvolution (μ.map g) (ν.map h) = (realConvolution μ ν).map q := by
  apply ProbabilityMeasure.toMeasure_injective
  change (((μ : Measure ℝ).map g).prod ((ν : Measure ℝ).map h)).map
      (fun z : ℝ × ℝ ↦ z.1 + z.2) =
    (((μ : Measure ℝ).prod (ν : Measure ℝ)).map (fun z : ℝ × ℝ ↦ z.1 + z.2)).map q
  rw [Measure.map_prod_map _ _ g.measurable h.measurable,
    Measure.map_map measurable_add (g.measurable.prodMap h.measurable),
    Measure.map_map q.measurable measurable_add]
  congr 1
  funext z
  change g.ratio * z.1 + g.shift + (h.ratio * z.2 + h.shift) =
    q.ratio * (z.1 + z.2) + q.shift
  rw [hr, hs, ← hb]
  ring

theorem normalizedDyadicEntropy_affine_le (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (g : RealSimilarity) {K : ℕ} (hK : |g.ratio| ≤ K) (n : ℕ) :
    normalizedDyadicEntropy (μ.map g) (g.hasBoundedSupport_map μ hμ) n ≤
      normalizedDyadicEntropy μ hμ n + Real.log (2 * K + 3 : ℝ) / ((n : ℝ) * Real.log 2) := by
  have h := div_le_div_of_nonneg_right (dyadicEntropy_map_affine_sub_le μ hμ g hK n)
    (show 0 ≤ (n : ℝ) * Real.log 2 by positivity)
  simp only [sub_div] at h
  unfold normalizedDyadicEntropy
  linarith

theorem normalizedDyadicEntropy_le_affine_add (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (g : RealSimilarity) {K : ℕ} (hK : |g.ratio|⁻¹ ≤ K) (n : ℕ) :
    normalizedDyadicEntropy μ hμ n ≤
      normalizedDyadicEntropy (μ.map g) (g.hasBoundedSupport_map μ hμ) n +
        Real.log (2 * K + 3 : ℝ) / ((n : ℝ) * Real.log 2) := by
  have h := div_le_div_of_nonneg_right (dyadicEntropy_le_map_affine_add μ hμ g hK n)
    (show 0 ≤ (n : ℝ) * Real.log 2 by positivity)
  simpa only [add_div, normalizedDyadicEntropy] using h

end ExactOverlaps.Entropy
