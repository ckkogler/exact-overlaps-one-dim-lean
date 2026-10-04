module

public import ExactOverlaps.VarianceEnergy.Basic
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Averaged interval mass

Integrating the mass of a sliding window of length `r` over all window origins
gives `r` times the total mass. This Tonelli identity is the normalization input
for the local variance functional.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace ExactOverlaps.VarianceEnergy

lemma lintegral_interval_mass (μ : Measure ℝ) [SFinite μ] (r : ℝ) :
    (∫⁻ a : ℝ, μ (Ico a (a + r))) = ENNReal.ofReal r * μ univ := by
  classical
  let f : ℝ → ℝ → ℝ≥0∞ := fun a x ↦ if x ∈ Ico a (a + r) then 1 else 0
  have hf : Measurable (Function.uncurry f) := by
    apply Measurable.ite _ measurable_const measurable_const
    exact (measurableSet_le measurable_fst measurable_snd).inter
      (measurableSet_lt measurable_snd (measurable_fst.add_const r))
  have hinner (a : ℝ) : (∫⁻ x, f a x ∂μ) = μ (Ico a (a + r)) := by
    simpa [f, Set.indicator_apply] using
      (lintegral_indicator_const (μ := μ) (s := Ico a (a + r)) measurableSet_Ico 1)
  have houter (x : ℝ) : (∫⁻ a, f a x) = ENNReal.ofReal r := by
    have he : (fun a ↦ f a x) =
        (Ioc (x - r) x).indicator (fun _ ↦ (1 : ℝ≥0∞)) := by
      funext a
      have hmem : x ∈ Ico a (a + r) ↔ a ∈ Ioc (x - r) x := by
        simp only [mem_Ico, mem_Ioc]
        constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
      simp only [f, Set.indicator_apply, hmem]
    rw [he, lintegral_indicator measurableSet_Ioc]
    simp [Real.volume_Ioc]
  calc
    (∫⁻ a, μ (Ico a (a + r))) = ∫⁻ a, ∫⁻ x, f a x ∂μ := by
      simp_rw [hinner]
    _ = ∫⁻ x, (∫⁻ a, f a x) ∂μ := lintegral_lintegral_swap hf.aemeasurable
    _ = ENNReal.ofReal r * μ univ := by simp_rw [houter]; exact lintegral_const _

lemma lintegral_interval_mass_probability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (r : ℝ) : (∫⁻ a : ℝ, μ (Ico a (a + r))) = ENNReal.ofReal r := by
  rw [lintegral_interval_mass]
  simp

end ExactOverlaps.VarianceEnergy
