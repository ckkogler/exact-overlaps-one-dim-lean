/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.ConvolutionDisintegration.WindowLaws
public import ExactOverlaps.VarianceEnergy.IntervalMass
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# The actual sliding-window disintegration

Interval origins have density equal to the mass of their length-r window,
divided by r. Tonelli's identity proves that this is a probability law and
that its mixture of normalized window restrictions is the original law.
This is the continuous origin form of averaging shifted grids.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace ExactOverlaps.ConvolutionDisintegration

def windowMixingLaw (μ : ProbabilityMeasure ℝ) {r : ℝ} (hr : 0 < r) : ProbabilityMeasure ℝ :=
  ⟨(ENNReal.ofReal r)⁻¹ • volume.withDensity (fun a : ℝ ↦ (μ : Measure ℝ) (Ico a (a + r))),
    ⟨by
      rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
        Measure.restrict_univ, VarianceEnergy.lintegral_interval_mass_probability, smul_eq_mul,
        ENNReal.inv_mul_cancel (by positivity : ENNReal.ofReal r ≠ 0) ENNReal.ofReal_ne_top]⟩⟩

lemma lintegral_windowMixingLaw (μ : ProbabilityMeasure ℝ) {r : ℝ} (hr : 0 < r)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ a, f a ∂(windowMixingLaw μ hr : Measure ℝ)) =
      (ENNReal.ofReal r)⁻¹ * ∫⁻ a : ℝ, (μ : Measure ℝ) (Ico a (a + r)) * f a := by
  change (∫⁻ a, f a ∂((ENNReal.ofReal r)⁻¹ • volume.withDensity
    (fun a : ℝ ↦ (μ : Measure ℝ) (Ico a (a + r))))) = _
  rw [lintegral_smul_measure, smul_eq_mul,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_windowMass (μ : Measure ℝ) r) hf]
  rfl

lemma lintegral_weighted_windowLaw (μ : ProbabilityMeasure ℝ) (r : ℝ)
    {E : Set ℝ} (hE : MeasurableSet E) :
    (∫⁻ a : ℝ, (μ : Measure ℝ) (Ico a (a + r)) * (windowLaw μ r a : Measure ℝ) E) =
      ENNReal.ofReal r * (μ : Measure ℝ) E := by
  have he (a : ℝ) : (μ : Measure ℝ) (Ico a (a + r)) * (windowLaw μ r a : Measure ℝ) E =
      (μ : Measure ℝ).restrict E (Ico a (a + r)) := by
    have h := congrArg (fun ν : Measure ℝ ↦ ν E) (windowMass_smul_windowLaw μ r a)
    simpa only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hE,
      Measure.restrict_apply measurableSet_Ico, inter_comm] using h
  simp_rw [he]
  rw [VarianceEnergy.lintegral_interval_mass, Measure.restrict_apply_univ]

def windowFamily (μ : ProbabilityMeasure ℝ) (r : ℝ) (a : ℝ) : FactorFamily :=
  singleLaw (windowLaw μ r a)

lemma measurable_windowFamily (μ : ProbabilityMeasure ℝ) (r : ℝ) :
    Measurable (windowFamily μ r) := measurable_singleLaw.comp (measurable_windowLaw μ r)

lemma familyMixture_windowFamily (μ : ProbabilityMeasure ℝ) {r : ℝ} (hr : 0 < r) :
    familyMixture (windowMixingLaw μ hr) (windowFamily μ r) (measurable_windowFamily μ r) = μ := by
  apply Subtype.ext
  apply Measure.ext
  intro E hE
  change ((windowMixingLaw μ hr : Measure ℝ).bind
    (familyKernel (windowFamily μ r) (measurable_windowFamily μ r))) E = _
  rw [Measure.bind_apply hE (familyKernel _ _).aemeasurable]
  have he (a : ℝ) : familyKernel (windowFamily μ r) (measurable_windowFamily μ r) a =
      (windowLaw μ r a : Measure ℝ) := by
    change (convolutionLaw (singleLaw (windowLaw μ r a)) : Measure ℝ) = _
    rw [convolutionLaw_singleLaw]
  simp_rw [he]
  have hm : Measurable (fun a ↦ (windowLaw μ r a : Measure ℝ) E) :=
    (Measure.measurable_coe hE).comp (measurable_subtype_coe.comp (measurable_windowLaw μ r))
  rw [lintegral_windowMixingLaw μ hr hm,
    lintegral_weighted_windowLaw μ r hE, ← mul_assoc,
    ENNReal.inv_mul_cancel (by positivity : ENNReal.ofReal r ≠ 0) ENNReal.ofReal_ne_top, one_mul]
  rfl

lemma isFamilyDisintegration_window (μ : ProbabilityMeasure ℝ) {r : ℝ} (hr : 0 < r) :
    IsFamilyDisintegration μ r (windowMixingLaw μ hr) (windowFamily μ r)
      (measurable_windowFamily μ r) := by
  refine ⟨familyMixture_windowFamily μ hr, Filter.Eventually.of_forall (fun a ↦ ?_)⟩
  exact (admissible_singleLaw_iff _ _).mpr (hasIntervalWidth_windowLaw μ hr.le a)

end ExactOverlaps.ConvolutionDisintegration
