/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.ConvolutionDisintegration.DiracRepresentation
public import ExactOverlaps.VarianceEnergy.ConditionalVariance

/-!
# Measurable normalized sliding-window laws

The component at an interval origin is the actual normalized restriction to
the half-open interval. Empty windows use a point mass at their origin.
The weighted measure and weighted variance identities include those empty
windows, and every component has the required interval width.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace ExactOverlaps.ConvolutionDisintegration

lemma measurable_windowMass (μ : Measure ℝ) [SFinite μ] (r : ℝ) :
    Measurable (fun a : ℝ ↦ μ (Ico a (a + r))) := by
  classical
  let f : ℝ → ℝ → ℝ≥0∞ := fun a x ↦ if x ∈ Ico a (a + r) then 1 else 0
  have hf : Measurable (Function.uncurry f) := by
    apply Measurable.ite _ measurable_const measurable_const
    exact (measurableSet_le measurable_fst measurable_snd).inter
      (measurableSet_lt measurable_snd (measurable_fst.add_const r))
  have he (a : ℝ) : (∫⁻ x, f a x ∂μ) = μ (Ico a (a + r)) := by
    simpa [f, Set.indicator_apply] using
      (lintegral_indicator_const (μ := μ) (s := Ico a (a + r)) measurableSet_Ico 1)
  simpa only [he] using (hf.lintegral_prod_right (ν := μ))

lemma measurable_windowRestriction (μ : Measure ℝ) [IsFiniteMeasure μ] (r : ℝ) :
    Measurable (fun a : ℝ ↦ μ.restrict (Ico a (a + r))) := by
  apply Measure.measurable_of_measurable_coe
  intro E hE
  simpa only [Measure.restrict_apply hE, Measure.restrict_apply measurableSet_Ico, inter_comm]
    using measurable_windowMass (μ.restrict E) r

lemma measurable_windowConditional (μ : Measure ℝ) [IsFiniteMeasure μ] (r : ℝ) :
    Measurable (fun a : ℝ ↦ cond μ (Ico a (a + r))) := by
  apply Measure.measurable_of_measurable_coe
  intro E hE
  change Measurable (fun a : ℝ ↦ (μ (Ico a (a + r)))⁻¹ * μ.restrict (Ico a (a + r)) E)
  exact (measurable_windowMass μ r).inv.mul
    ((Measure.measurable_coe hE).comp (measurable_windowRestriction μ r))

def windowLaw (μ : ProbabilityMeasure ℝ) (r a : ℝ) : ProbabilityMeasure ℝ :=
  ⟨if (μ : Measure ℝ) (Ico a (a + r)) = 0 then Measure.dirac a
    else cond (μ : Measure ℝ) (Ico a (a + r)), by
      split_ifs with h
      · infer_instance
      · exact cond_isProbabilityMeasure h⟩

lemma windowLaw_toMeasure (μ : ProbabilityMeasure ℝ) (r a : ℝ) :
    (windowLaw μ r a : Measure ℝ) =
      if (μ : Measure ℝ) (Ico a (a + r)) = 0 then Measure.dirac a
      else cond (μ : Measure ℝ) (Ico a (a + r)) := rfl

lemma measurable_windowLaw (μ : ProbabilityMeasure ℝ) (r : ℝ) :
    Measurable (windowLaw μ r) := by
  have hm : Measurable (fun a ↦ (windowLaw μ r a : Measure ℝ)) := by
    simp only [windowLaw_toMeasure]
    exact Measurable.ite (measurableSet_eq_fun (measurable_windowMass (μ : Measure ℝ) r)
      measurable_const) Measure.measurable_dirac (measurable_windowConditional (μ : Measure ℝ) r)
  exact hm.subtype_mk

lemma windowMass_smul_windowLaw (μ : ProbabilityMeasure ℝ) (r a : ℝ) :
    (μ : Measure ℝ) (Ico a (a + r)) • (windowLaw μ r a : Measure ℝ) =
      (μ : Measure ℝ).restrict (Ico a (a + r)) := by
  rw [windowLaw_toMeasure]
  split_ifs with h
  · rw [h, zero_smul, Measure.restrict_eq_zero.mpr h]
  · rw [ProbabilityTheory.cond, smul_smul, ENNReal.mul_inv_cancel h (measure_ne_top _ _), one_smul]

lemma hasIntervalWidth_windowLaw (μ : ProbabilityMeasure ℝ) {r : ℝ}
    (hr : 0 ≤ r) (a : ℝ) : HasIntervalWidth (windowLaw μ r a) r := by
  refine ⟨a, ?_⟩
  rw [windowLaw_toMeasure]
  split_ifs with h
  · have ha : a ∈ Icc a (a + r) := ⟨le_rfl, by linarith⟩
    simpa using ha
  · exact (ae_cond_mem (μ := (μ : Measure ℝ)) measurableSet_Ico).mono
      (fun _ hx ↦ ⟨hx.1, hx.2.le⟩)

lemma localVarianceMass_windowLaw (μ : ProbabilityMeasure ℝ) (r a : ℝ) :
    VarianceEnergy.localVarianceMass (μ : Measure ℝ) a r =
      (μ : Measure ℝ) (Ico a (a + r)) *
        ENNReal.ofReal (variance (id : ℝ → ℝ) (windowLaw μ r a : Measure ℝ)) := by
  rw [VarianceEnergy.localVarianceMass_eq_cond_variance, windowLaw_toMeasure]
  split_ifs with h
  · simp only [h, zero_mul]
  · rfl

lemma variance_windowLaw_le (μ : ProbabilityMeasure ℝ) {r : ℝ} (hr : 0 ≤ r) (a : ℝ) :
    variance (id : ℝ → ℝ) (windowLaw μ r a : Measure ℝ) ≤ r ^ 2 / 4 := by
  obtain ⟨b, hb⟩ := hasIntervalWidth_windowLaw μ hr a
  have h := variance_le_sq_of_bounded hb measurable_id.aemeasurable
  have he : ((b + r - b) / 2) ^ 2 = r ^ 2 / 4 := by ring
  exact h.trans_eq he

end ExactOverlaps.ConvolutionDisintegration
