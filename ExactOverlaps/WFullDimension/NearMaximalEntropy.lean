/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.WFullDimension.WEntropy

/-!
Uniform small-cost thresholds give entropy between doubling scales
arbitrarily close to its sharp maximum. The constants precede the law and
physical mesh, using the full bounded-factor entropy-growth theorem.
-/

@[expose] public section

noncomputable section
open MeasureTheory

namespace ExactOverlaps.WFullDimension

open ConvolutionDisintegration Entropy ScaleEntropy GaussianEntropyGrowth

theorem exists_W_threshold_for_entropy {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∃ b > 0, ∀ (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ)
      (r : ℝ) (hr : 0 < r), W μ (δ * r) < b →
        Real.log 2 - ε < entropyBetween μ hμ r hr (2 * r) (by positivity) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let e := min (ε / 2) (Real.log 2 / 2)
  have he : 0 < e := lt_min (half_pos hε) (half_pos hlog)
  have heε : e ≤ ε / 2 := min_le_left _ _
  have helog : e ≤ Real.log 2 / 2 := min_le_right _ _
  obtain ⟨δ, hδ, A, _hA, hgrowth⟩ := admissible_factor_entropy_growth 2 (by norm_num) he
  let K := Real.exp (4 * A / δ ^ 2)
  have hK : 0 < K := Real.exp_pos _
  let b := ε / (4 * K * Real.log 2)
  have hb : 0 < b := div_pos hε (by positivity)
  refine ⟨δ, hδ, b, hb, ?_⟩
  intro μ hμ r hr hW
  have hL : 0 ≤ Real.log 2 - e := by linarith
  have hbound := entropy_lower_bound_of_W_lt hδ hL
    (fun r hr c hc hv ↦ (hgrowth r hr c hc hv).le) μ hμ r hr hW
  change (Real.log 2 - e) * (1 - K * b) ≤ _ at hbound
  have heq : Real.log 2 * (K * b) = ε / 4 := by
    dsimp [b]
    field_simp
  have hproduct : (Real.log 2 - e) * (K * b) ≤ ε / 4 := by
    rw [← heq]
    exact mul_le_mul_of_nonneg_right (sub_le_self _ he.le) (mul_pos hK hb).le
  have hclose : Real.log 2 - ε < (Real.log 2 - e) * (1 - K * b) := by
    nlinarith
  exact hclose.trans_le hbound

end ExactOverlaps.WFullDimension
