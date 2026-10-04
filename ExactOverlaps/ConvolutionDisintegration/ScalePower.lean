/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.ConvolutionDisintegration.DiracRepresentation
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Topology.Order.Monotone

/-!
# The power inequality between scales

An admissible scale-r family remains admissible at every larger scale s.
Its cost changes by the power r²/s². Integral Jensen for this concave power
and continuity at the nonnegative infimum prove the same inequality for W,
including when the infimum is zero or is not attained.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace ExactOverlaps.ConvolutionDisintegration

lemma IsDisintegration.mono {μ : ProbabilityMeasure ℝ} {r s : ℝ}
    {θ : ProbabilityMeasure FactorFamily} (h : IsDisintegration μ r θ) (hrs : r ≤ s) :
    IsDisintegration μ s θ := ⟨h.1, h.2.mono (fun _ hc ↦ hc.mono hrs)⟩

lemma cost_scale_power {r : ℝ} (hr : r ≠ 0) (s : ℝ) (c : FactorFamily) :
    cost s c = (cost r c) ^ (r ^ 2 / s ^ 2) := by
  unfold cost
  rw [← Real.exp_mul]
  congr 1
  field_simp

lemma averageCost_scale_power_le {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s)
    (θ : ProbabilityMeasure FactorFamily) :
    averageCost s θ ≤ (averageCost r θ) ^ (r ^ 2 / s ^ 2) := by
  have hs : 0 < s := hr.trans_le hrs
  have hq0 : 0 ≤ r ^ 2 / s ^ 2 := div_nonneg (sq_nonneg r) (sq_nonneg s)
  have hq1 : r ^ 2 / s ^ 2 ≤ 1 := by
    apply (div_le_one (sq_pos_of_pos hs)).mpr
    nlinarith
  have he : (fun c : FactorFamily ↦ (cost r c) ^ (r ^ 2 / s ^ 2)) = cost s :=
    funext (fun c ↦ (cost_scale_power hr.ne' s c).symm)
  have hi : Integrable ((fun v : ℝ ↦ v ^ (r ^ 2 / s ^ 2)) ∘ cost r)
      (θ : Measure FactorFamily) := by
    change Integrable (fun c ↦ (cost r c) ^ (r ^ 2 / s ^ 2)) (θ : Measure FactorFamily)
    rw [he]
    exact integrable_cost s θ
  have h := (Real.concaveOn_rpow hq0 hq1).le_map_integral
    (Real.continuous_rpow_const hq0).continuousOn isClosed_Ici
    (Filter.Eventually.of_forall (fun c ↦ (cost_pos r c).le)) (integrable_cost r θ) hi
  rw [he] at h
  exact h

theorem W_scale_power_le {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s)
    (μ : ProbabilityMeasure ℝ) : W μ s ≤ (W μ r) ^ (r ^ 2 / s ^ 2) := by
  have hq : 0 ≤ r ^ 2 / s ^ 2 := div_nonneg (sq_nonneg r) (sq_nonneg s)
  have hm : MonotoneOn (fun v : ℝ ↦ v ^ (r ^ 2 / s ^ 2)) (costValues μ r) := by
    intro x hx y _ hxy
    obtain ⟨θ, _, rfl⟩ := hx
    exact Real.rpow_le_rpow (averageCost_nonneg r θ) hxy hq
  have he : (W μ r) ^ (r ^ 2 / s ^ 2) =
      sInf ((fun v : ℝ ↦ v ^ (r ^ 2 / s ^ 2)) '' costValues μ r) :=
    MonotoneOn.map_csInf_of_continuousWithinAt
      (Real.continuous_rpow_const hq).continuousAt.continuousWithinAt hm
      (costValues_nonempty hr.le μ) (costValues_bddBelow μ r)
  rw [he]
  apply le_csInf ((costValues_nonempty hr.le μ).image _)
  rintro _ ⟨v, ⟨θ, hθ, rfl⟩, rfl⟩
  exact (W_le_averageCost (hθ.mono hrs)).trans (averageCost_scale_power_le hr hrs θ)

end ExactOverlaps.ConvolutionDisintegration
