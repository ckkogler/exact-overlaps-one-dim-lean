module

public import ExactOverlaps.VarianceEnergy.SupportBounds
public import ExactOverlaps.Probability.PoissonKernels

/-!
# The variance-energy tail

Above scale `R`, a support interval of length `D` bounds the logarithmic
variance integral by `D²/(2R²)`. The bound is stated directly for the tail,
so it is meaningful even when the full energy is infinite.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace ExactOverlaps.VarianceEnergy

/-- Variance energy strictly above scale `R`. The endpoint has Lebesgue mass zero. -/
def energyAbove (μ : Measure ℝ) (R : ℝ) : ℝ≥0∞ :=
  ∫⁻ r in Ioi R, normalizedLocalVariance μ r * ENNReal.ofReal (1 / r)

lemma energyAbove_support_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {b D R : ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ Icc b (b + D)) (hR : 0 < R) :
    energyAbove μ R ≤ ENNReal.ofReal (D ^ 2 / (2 * R ^ 2)) := by
  have hkernel : (∫⁻ r in Ioi R, ENNReal.ofReal (1 / r ^ 3)) =
      ENNReal.ofReal (1 / (2 * R ^ 2)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (Poisson.integrableOn_inv_cube hR)]
    · rw [Poisson.integral_inv_cube hR]
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have hr0 : 0 < r := hR.trans hr
      positivity
  calc
    energyAbove μ R ≤ ∫⁻ r in Ioi R,
        ENNReal.ofReal (D ^ 2) * ENNReal.ofReal (1 / r ^ 3) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have hr0 : 0 < r := hR.trans hr
      calc
        normalizedLocalVariance μ r * ENNReal.ofReal (1 / r) ≤
            ENNReal.ofReal (D ^ 2 / r ^ 2) * ENNReal.ofReal (1 / r) :=
          mul_le_mul_of_nonneg_right (normalizedLocalVariance_support_le μ hμ hr0)
            zero_le
        _ = _ := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
    _ = ENNReal.ofReal (D ^ 2) * ENNReal.ofReal (1 / (2 * R ^ 2)) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hkernel]
    _ = ENNReal.ofReal (D ^ 2 / (2 * R ^ 2)) := by
      rw [← ENNReal.ofReal_mul (sq_nonneg D)]
      congr 1
      ring

lemma energyAbove_ne_top (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {b D R : ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ Icc b (b + D)) (hR : 0 < R) :
    energyAbove μ R ≠ ∞ :=
  ne_of_lt (lt_of_le_of_lt (energyAbove_support_le μ hμ hR) ENNReal.ofReal_lt_top)

end ExactOverlaps.VarianceEnergy
