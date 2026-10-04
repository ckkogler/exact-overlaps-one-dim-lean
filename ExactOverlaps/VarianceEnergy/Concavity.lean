module

public import ExactOverlaps.VarianceEnergy.Measurable

/-!
# Concavity under mixtures

Local variance is the infimum of linear squared-error functionals. Its
concavity passes through the origin and scale integrals. The inequalities
below apply to all nonnegative mixture weights, including probability mixtures.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace ExactOverlaps.VarianceEnergy

lemma normalizedLocalVariance_mixture_le (s t : ℝ≥0∞) (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (r : ℝ) :
    s * normalizedLocalVariance μ r + t * normalizedLocalVariance ν r ≤
      normalizedLocalVariance (s • μ + t • ν) r := by
  have hμ : Measurable (fun a : ℝ ↦ localVarianceMass μ a r) :=
    (measurable_localVarianceMass μ).comp (measurable_id.prodMk measurable_const)
  have hν : Measurable (fun a : ℝ ↦ localVarianceMass ν a r) :=
    (measurable_localVarianceMass ν).comp (measurable_id.prodMk measurable_const)
  calc
    s * normalizedLocalVariance μ r + t * normalizedLocalVariance ν r =
        ENNReal.ofReal (4 / r ^ 3) *
          ((∫⁻ a : ℝ, s * localVarianceMass μ a r) +
           (∫⁻ a : ℝ, t * localVarianceMass ν a r)) := by
      rw [lintegral_const_mul s hμ, lintegral_const_mul t hν]
      unfold normalizedLocalVariance
      ring
    _ = ENNReal.ofReal (4 / r ^ 3) *
        ∫⁻ a : ℝ, s * localVarianceMass μ a r + t * localVarianceMass ν a r := by
      rw [lintegral_add_left (hμ.const_mul s)]
    _ ≤ normalizedLocalVariance (s • μ + t • ν) r := by
      apply mul_le_mul_of_nonneg_left _ zero_le
      exact lintegral_mono (fun a ↦ localVarianceMass_mixture_le s t μ ν a r)

lemma energyBelow_mixture_le (s t : ℝ≥0∞) (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (R : ℝ) :
    s * energyBelow μ R + t * energyBelow ν R ≤
      energyBelow (s • μ + t • ν) R := by
  have hμ : Measurable (fun r : ℝ ↦
      normalizedLocalVariance μ r * ENNReal.ofReal (1 / r)) :=
    (measurable_normalizedLocalVariance μ).mul (by fun_prop)
  have hν : Measurable (fun r : ℝ ↦
      normalizedLocalVariance ν r * ENNReal.ofReal (1 / r)) :=
    (measurable_normalizedLocalVariance ν).mul (by fun_prop)
  calc
    s * energyBelow μ R + t * energyBelow ν R =
        ∫⁻ r in Ioo (0 : ℝ) R,
          s * (normalizedLocalVariance μ r * ENNReal.ofReal (1 / r)) +
          t * (normalizedLocalVariance ν r * ENNReal.ofReal (1 / r)) := by
      rw [lintegral_add_left (hμ.const_mul s), lintegral_const_mul s hμ,
        lintegral_const_mul t hν]
      rfl
    _ ≤ energyBelow (s • μ + t • ν) R := by
      apply lintegral_mono
      intro r
      calc
        _ = (s * normalizedLocalVariance μ r + t * normalizedLocalVariance ν r) *
            ENNReal.ofReal (1 / r) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (normalizedLocalVariance_mixture_le s t μ ν r) zero_le

lemma energy_mixture_le (s t : ℝ≥0∞) (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    s * energy μ + t * energy ν ≤ energy (s • μ + t • ν) := by
  have hμ : Measurable (fun r : ℝ ↦
      normalizedLocalVariance μ r * ENNReal.ofReal (1 / r)) :=
    (measurable_normalizedLocalVariance μ).mul (by fun_prop)
  have hν : Measurable (fun r : ℝ ↦
      normalizedLocalVariance ν r * ENNReal.ofReal (1 / r)) :=
    (measurable_normalizedLocalVariance ν).mul (by fun_prop)
  calc
    s * energy μ + t * energy ν = ∫⁻ r in Ioi (0 : ℝ),
        s * (normalizedLocalVariance μ r * ENNReal.ofReal (1 / r)) +
        t * (normalizedLocalVariance ν r * ENNReal.ofReal (1 / r)) := by
      rw [lintegral_add_left (hμ.const_mul s), lintegral_const_mul s hμ,
        lintegral_const_mul t hν]
      rfl
    _ ≤ energy (s • μ + t • ν) := by
      apply lintegral_mono
      intro r
      calc
        _ = (s * normalizedLocalVariance μ r + t * normalizedLocalVariance ν r) *
            ENNReal.ofReal (1 / r) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (normalizedLocalVariance_mixture_le s t μ ν r) zero_le

end ExactOverlaps.VarianceEnergy
