module

public import ExactOverlaps.VarianceEnergy.Normalization

/-!
# Bounds from the support interval

Using the midpoint of a fixed support interval bounds local variance by the
squared support diameter divided by the squared observation scale.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace ExactOverlaps.VarianceEnergy

lemma sq_sub_midpoint_le_Icc {b D x : ℝ} (hx : x ∈ Icc b (b + D)) :
    (x - (b + D / 2)) ^ 2 ≤ D ^ 2 / 4 := by
  have hleft : -(D / 2) ≤ x - (b + D / 2) := by linarith [hx.1]
  have hright : x - (b + D / 2) ≤ D / 2 := by linarith [hx.2]
  nlinarith [mul_nonneg (sub_nonneg.mpr hleft) (sub_nonneg.mpr hright)]

lemma localVarianceMass_support_le (μ : Measure ℝ) {b D : ℝ}
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc b (b + D)) (a r : ℝ) :
    localVarianceMass μ a r ≤ ENNReal.ofReal (D ^ 2 / 4) * μ (Ico a (a + r)) := by
  apply (localVarianceMass_le μ a r (b + D / 2)).trans
  calc
    localQuadraticError μ a r (b + D / 2) ≤
        ∫⁻ _ in Ico a (a + r), ENNReal.ofReal (D ^ 2 / 4) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_of_ae hμ] with x hx
      exact ENNReal.ofReal_le_ofReal (sq_sub_midpoint_le_Icc hx)
    _ = _ := by simp

lemma normalizedLocalVariance_support_le_mass (μ : Measure ℝ) [SFinite μ]
    {b D r : ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ Icc b (b + D)) (hr : 0 < r) :
    normalizedLocalVariance μ r ≤ ENNReal.ofReal (D ^ 2 / r ^ 2) * μ univ := by
  have hlocal : (∫⁻ a : ℝ, localVarianceMass μ a r) ≤
      ENNReal.ofReal (D ^ 2 / 4) * (ENNReal.ofReal r * μ univ) := by
    calc
      (∫⁻ a : ℝ, localVarianceMass μ a r) ≤
          ∫⁻ a : ℝ, ENNReal.ofReal (D ^ 2 / 4) * μ (Ico a (a + r)) :=
        lintegral_mono (fun a ↦ localVarianceMass_support_le μ hμ a r)
      _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_interval_mass]
  have hfactor : ENNReal.ofReal (4 / r ^ 3) *
      (ENNReal.ofReal (D ^ 2 / 4) * ENNReal.ofReal r) =
        ENNReal.ofReal (D ^ 2 / r ^ 2) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp [ne_of_gt hr]
  calc
    normalizedLocalVariance μ r ≤ ENNReal.ofReal (4 / r ^ 3) *
        (ENNReal.ofReal (D ^ 2 / 4) * (ENNReal.ofReal r * μ univ)) :=
      mul_le_mul_of_nonneg_left hlocal zero_le
    _ = (ENNReal.ofReal (4 / r ^ 3) *
        (ENNReal.ofReal (D ^ 2 / 4) * ENNReal.ofReal r)) * μ univ := by ac_rfl
    _ = ENNReal.ofReal (D ^ 2 / r ^ 2) * μ univ := by rw [hfactor]

lemma normalizedLocalVariance_support_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {b D r : ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ Icc b (b + D)) (hr : 0 < r) :
    normalizedLocalVariance μ r ≤ ENNReal.ofReal (D ^ 2 / r ^ 2) := by
  simpa using normalizedLocalVariance_support_le_mass μ hμ hr

end ExactOverlaps.VarianceEnergy
