/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.WFullDimension.StationaryScale
public import ExactOverlaps.WFullDimension.EntropyLimit

/-!
Proposition 3.10: a self-similar measure with convolution-disintegration
cost tending to zero along positive scales approaching zero has standard
Hausdorff dimension one. All signed finite contracting systems are allowed.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace ExactOverlaps.WFullDimension

open ConvolutionDisintegration

theorem dimension_eq_one_of_W_sequence {ι : Type*} [Fintype ι]
    (S : SelfSimilar.System ι) (μ : ProbabilityMeasure ℝ)
    (hμ : S.IsStationary (μ : Measure ℝ))
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n)
    (hW : Tendsto (fun n ↦ W μ (r n)) atTop (𝓝 0)) :
    lowerHausdorffDimension (μ : Measure ℝ) = 1 :=
  dimension_eq_one_of_W_tendsto S μ hμ
    (stationary_W_tendsto_zero_of_sequence S μ hμ hr hW)

/-- Proposition 3.10, with the source's positive scale sequence tending to zero. -/
theorem proposition_3_10 {ι : Type*} [Fintype ι]
    (S : SelfSimilar.System ι) (μ : ProbabilityMeasure ℝ)
    (hμ : S.IsStationary (μ : Measure ℝ))
    (hscales : ∃ r : ℕ → ℝ, (∀ n, 0 < r n) ∧ Tendsto r atTop (𝓝 0) ∧
      Tendsto (fun n ↦ W μ (r n)) atTop (𝓝 0)) :
    lowerHausdorffDimension (μ : Measure ℝ) = 1 := by
  obtain ⟨r, hr, _hrzero, hW⟩ := hscales
  exact dimension_eq_one_of_W_sequence S μ hμ hr hW

end ExactOverlaps.WFullDimension
