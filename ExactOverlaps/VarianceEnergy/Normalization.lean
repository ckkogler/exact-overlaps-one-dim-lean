module

public import ExactOverlaps.VarianceEnergy.Midpoint
public import ExactOverlaps.VarianceEnergy.IntervalMass

/-!
# Normalization of the local variance

The midpoint estimate and the sliding-window mass identity give `V ≤ 1` for
probability measures. No bounded-support assumption is needed for this estimate.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace ExactOverlaps.VarianceEnergy

lemma lintegral_localVarianceMass_le (μ : Measure ℝ) [SFinite μ] (r : ℝ) :
    (∫⁻ a : ℝ, localVarianceMass μ a r) ≤
      ENNReal.ofReal (r ^ 2 / 4) * (ENNReal.ofReal r * μ univ) := by
  calc
    (∫⁻ a : ℝ, localVarianceMass μ a r) ≤
        ∫⁻ a : ℝ, ENNReal.ofReal (r ^ 2 / 4) * μ (Ico a (a + r)) :=
      lintegral_mono (fun a ↦ localVarianceMass_midpoint_le μ a r)
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_interval_mass]

lemma normalizedLocalVariance_le_mass (μ : Measure ℝ) [SFinite μ] {r : ℝ}
    (hr : 0 < r) : normalizedLocalVariance μ r ≤ μ univ := by
  have hnorm : ENNReal.ofReal (4 / r ^ 3) *
      (ENNReal.ofReal (r ^ 2 / 4) * ENNReal.ofReal r) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    have heq : 4 / r ^ 3 * (r ^ 2 / 4 * r) = 1 := by
      field_simp [ne_of_gt hr]
    rw [heq, ENNReal.ofReal_one]
  calc
    normalizedLocalVariance μ r ≤ ENNReal.ofReal (4 / r ^ 3) *
        (ENNReal.ofReal (r ^ 2 / 4) * (ENNReal.ofReal r * μ univ)) :=
      mul_le_mul_of_nonneg_left (lintegral_localVarianceMass_le μ r) zero_le
    _ = (ENNReal.ofReal (4 / r ^ 3) *
        (ENNReal.ofReal (r ^ 2 / 4) * ENNReal.ofReal r)) * μ univ := by ac_rfl
    _ = μ univ := by rw [hnorm, one_mul]

lemma normalizedLocalVariance_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 < r) : normalizedLocalVariance μ r ≤ 1 := by
  simpa using normalizedLocalVariance_le_mass μ hr

@[simp] lemma normalizedLocalVariance_dirac (x r : ℝ) :
    normalizedLocalVariance (Measure.dirac x) r = 0 := by
  simp [normalizedLocalVariance]

@[simp] lemma energyBelow_dirac (x R : ℝ) : energyBelow (Measure.dirac x) R = 0 := by
  simp [energyBelow]

@[simp] lemma energy_dirac (x : ℝ) : energy (Measure.dirac x) = 0 := by
  simp [energy]

end ExactOverlaps.VarianceEnergy
