/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.ConvolutionDisintegration.FactorScaling
public import ExactOverlaps.ConvolutionDisintegration.DiracRepresentation
public import Mathlib.Probability.Kernel.Composition.Lemmas

/-!
# Signed scaling covariance of W

Dilation of each actual factor induces a measurable pushforward of the
mixing law. Its mixture and cost are exactly the expected dilations.
Applying the construction in both directions proves equality of infima.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace ExactOverlaps.ConvolutionDisintegration

lemma familyKernel_scaleFamily (a : ℝ) :
    familyKernel (scaleFamily a) (measurable_scaleFamily a) =
      convolutionKernel.map (fun x ↦ a * x) := by
  ext1 c
  change (convolutionLaw (scaleFamily a c) : Measure ℝ) = _
  rw [convolutionLaw_scaleFamily, Kernel.map_apply _ (by fun_prop)]
  rfl

lemma familyMixture_scaleFamily (a : ℝ) (θ : ProbabilityMeasure FactorFamily) :
    familyMixture θ (scaleFamily a) (measurable_scaleFamily a) = scaleLaw a (mixture θ) := by
  apply Subtype.ext
  change familyKernel (scaleFamily a) (measurable_scaleFamily a) ∘ₘ (θ : Measure FactorFamily) =
    (convolutionKernel ∘ₘ (θ : Measure FactorFamily)).map (fun x ↦ a * x)
  rw [familyKernel_scaleFamily, Measure.map_comp _ _ (by fun_prop)]

lemma isDisintegration_scaleFamily (a : ℝ) {μ : ProbabilityMeasure ℝ} {r : ℝ}
    {θ : ProbabilityMeasure FactorFamily} (hθ : IsDisintegration μ r θ) :
    IsDisintegration (scaleLaw a μ) (|a| * r) (θ.map (scaleFamily a)) := by
  apply (isDisintegration_map_iff _ _ θ _ (measurable_scaleFamily a)).mpr
  constructor
  · rw [familyMixture_scaleFamily, hθ.1]
  · exact hθ.2.mono (fun _ hc ↦ admissible_scaleFamily a hc)

lemma averageCost_scaleFamily {a r : ℝ} (ha : a ≠ 0) (hr : 0 < r)
    (θ : ProbabilityMeasure FactorFamily) :
    averageCost (|a| * r) (θ.map (scaleFamily a)) = averageCost r θ := by
  rw [averageCost_map_eq _ _ (measurable_scaleFamily a)]
  simp only [cost_scaleFamily ha hr]
  rfl

lemma W_scaleLaw_mul_le {a r : ℝ} (ha : a ≠ 0) (hr : 0 < r)
    (μ : ProbabilityMeasure ℝ) : W (scaleLaw a μ) (|a| * r) ≤ W μ r := by
  apply le_csInf (costValues_nonempty hr.le μ)
  rintro _ ⟨θ, hθ, rfl⟩
  exact (W_le_averageCost (isDisintegration_scaleFamily a hθ)).trans_eq
    (averageCost_scaleFamily ha hr θ)

theorem W_scaleLaw_mul {a r : ℝ} (ha : a ≠ 0) (hr : 0 < r)
    (μ : ProbabilityMeasure ℝ) : W (scaleLaw a μ) (|a| * r) = W μ r := by
  apply le_antisymm (W_scaleLaw_mul_le ha hr μ)
  have h := W_scaleLaw_mul_le (inv_ne_zero ha) (mul_pos (abs_pos.mpr ha) hr) (scaleLaw a μ)
  rw [scaleLaw_inverse ha, abs_inv, inv_mul_cancel_left₀ (abs_ne_zero.mpr ha)] at h
  exact h

theorem W_scaleLaw {a r : ℝ} (ha : a ≠ 0) (hr : 0 < r)
    (μ : ProbabilityMeasure ℝ) : W (scaleLaw a μ) r = W μ (r / |a|) := by
  have h := W_scaleLaw_mul ha (div_pos hr (abs_pos.mpr ha)) μ
  have he : |a| * (r / |a|) = r := by field_simp
  rwa [he] at h

end ExactOverlaps.ConvolutionDisintegration
