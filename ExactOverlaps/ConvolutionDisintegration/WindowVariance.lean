/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.ConvolutionDisintegration.WindowMixture
public import ExactOverlaps.VarianceEnergy.Normalization

/-!
# Mean normalized variance of the sliding-window disintegration

The normalized variance of every component belongs to the unit interval.
Its genuine integral against the interval-origin probability law equals
the original normalized local-variance functional, with all constants kept.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace ExactOverlaps.ConvolutionDisintegration

def windowNormalizedVariance (μ : ProbabilityMeasure ℝ) (r a : ℝ) : ℝ :=
  4 / r ^ 2 * variance (id : ℝ → ℝ) (windowLaw μ r a : Measure ℝ)

lemma measurable_windowNormalizedVariance (μ : ProbabilityMeasure ℝ) (r : ℝ) :
    Measurable (windowNormalizedVariance μ r) :=
  measurable_const.mul (measurable_variance.comp (measurable_windowLaw μ r))

lemma windowNormalizedVariance_nonneg (μ : ProbabilityMeasure ℝ) (r a : ℝ) :
    0 ≤ windowNormalizedVariance μ r a :=
  mul_nonneg (div_nonneg (by norm_num) (sq_nonneg _)) (variance_nonneg _ _)

lemma windowNormalizedVariance_le_one (μ : ProbabilityMeasure ℝ) {r : ℝ}
    (hr : 0 < r) (a : ℝ) : windowNormalizedVariance μ r a ≤ 1 := by
  have h := mul_le_mul_of_nonneg_left (variance_windowLaw_le μ hr.le a)
    (show 0 ≤ 4 / r ^ 2 by positivity)
  have he : 4 / r ^ 2 * (r ^ 2 / 4) = 1 := by field_simp
  exact h.trans_eq he

lemma integrable_windowNormalizedVariance (μ : ProbabilityMeasure ℝ) {r : ℝ} (hr : 0 < r) :
    Integrable (windowNormalizedVariance μ r) (windowMixingLaw μ hr : Measure ℝ) := by
  apply memLp_one_iff_integrable.mp
  exact MemLp.of_bound (measurable_windowNormalizedVariance μ r).aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun a ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (windowNormalizedVariance_nonneg μ r a)]
      exact windowNormalizedVariance_le_one μ hr a))

lemma lintegral_windowNormalizedVariance (μ : ProbabilityMeasure ℝ) {r : ℝ} (hr : 0 < r) :
    (∫⁻ a, ENNReal.ofReal (windowNormalizedVariance μ r a)
      ∂(windowMixingLaw μ hr : Measure ℝ)) =
        VarianceEnergy.normalizedLocalVariance (μ : Measure ℝ) r := by
  rw [lintegral_windowMixingLaw μ hr (measurable_windowNormalizedVariance μ r).ennreal_ofReal]
  have he (a : ℝ) : (μ : Measure ℝ) (Ico a (a + r)) *
      ENNReal.ofReal (windowNormalizedVariance μ r a) =
      ENNReal.ofReal (4 / r ^ 2) * VarianceEnergy.localVarianceMass (μ : Measure ℝ) a r := by
    rw [windowNormalizedVariance, ENNReal.ofReal_mul (by positivity), localVarianceMass_windowLaw]
    ac_rfl
  simp_rw [he]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc]
  have hc : (ENNReal.ofReal r)⁻¹ * ENNReal.ofReal (4 / r ^ 2) = ENNReal.ofReal (4 / r ^ 3) := by
    rw [← ENNReal.ofReal_inv_of_pos hr, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  rw [hc]
  rfl

theorem integral_windowNormalizedVariance (μ : ProbabilityMeasure ℝ) {r : ℝ} (hr : 0 < r) :
    (∫ a, windowNormalizedVariance μ r a ∂(windowMixingLaw μ hr : Measure ℝ)) =
      (VarianceEnergy.normalizedLocalVariance (μ : Measure ℝ) r).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (windowNormalizedVariance_nonneg μ r))
    (measurable_windowNormalizedVariance μ r).aestronglyMeasurable,
    lintegral_windowNormalizedVariance μ hr]

end ExactOverlaps.ConvolutionDisintegration
