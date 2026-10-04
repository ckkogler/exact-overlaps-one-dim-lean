module

public import ExactOverlaps.VarianceEnergy.Translation
public import Mathlib.MeasureTheory.Measure.Interval
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Reflection invariance

Reflection exchanges the two endpoint conventions of a half-open window.
A finite or s-finite law has only countably many atoms, so the endpoints have
zero mass for almost every window origin. This is the required justification
for the signed affine case.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace ExactOverlaps.VarianceEnergy

lemma ae_singleton_eq_zero_comp (μ : Measure ℝ) [SFinite μ] (f : ℝ → ℝ)
    (hf : Function.Injective f) : ∀ᵐ a : ℝ, μ {f a} = 0 := by
  have hc : {x : ℝ | 0 < μ {x}}.Countable := by
    simpa only [id_eq, ofPred_eq_eq_singleton] using
      (Measure.countable_meas_level_set_pos (μ := μ) (g := id) measurable_id)
  filter_upwards [(hc.preimage hf).ae_notMem volume] with a ha
  exact le_antisymm (not_lt.mp ha) zero_le

lemma localQuadraticError_map_neg_of_no_atoms (μ : Measure ℝ) (a r c : ℝ)
    (ha : μ {-a - r} = 0) (hb : μ {-a} = 0) :
    localQuadraticError (μ.map (fun x ↦ -x)) a r c =
      localQuadraticError μ (-a - r) r (-c) := by
  have hpre : (fun x : ℝ ↦ -x) ⁻¹' Ico a (a + r) =
      Ioc (-a - r) (-a - r + r) := by
    ext x
    simp only [mem_preimage, mem_Ico, mem_Ioc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have hrestr : μ.restrict (Ioc (-a - r) (-a - r + r)) =
      μ.restrict (Ico (-a - r) (-a - r + r)) :=
    (Measure.restrict_congr_set (Ico_ae_eq_Ioc' ha (by simpa using hb))).symm
  unfold localQuadraticError
  rw [setLIntegral_map measurableSet_Ico (by fun_prop) (by fun_prop), hpre, hrestr]
  apply lintegral_congr
  intro x
  congr 1
  ring

lemma localVarianceMass_map_neg_of_no_atoms (μ : Measure ℝ) (a r : ℝ)
    (ha : μ {-a - r} = 0) (hb : μ {-a} = 0) :
    localVarianceMass (μ.map (fun x ↦ -x)) a r = localVarianceMass μ (-a - r) r := by
  simp only [localVarianceMass, localQuadraticError_map_neg_of_no_atoms μ a r _ ha hb]
  have hsurj : Function.Surjective (fun c : ℝ ↦ -c) := by
    intro x
    exact ⟨-x, neg_neg x⟩
  exact hsurj.iInf_comp (fun c ↦ localQuadraticError μ (-a - r) r c)

lemma normalizedLocalVariance_map_neg (μ : Measure ℝ) [SFinite μ] (r : ℝ) :
    normalizedLocalVariance (μ.map (fun x ↦ -x)) r = normalizedLocalVariance μ r := by
  have hleft := ae_singleton_eq_zero_comp μ (fun a : ℝ ↦ -a - r) (by
    intro a b h
    linarith)
  have hright := ae_singleton_eq_zero_comp μ (fun a : ℝ ↦ -a) neg_injective
  unfold normalizedLocalVariance
  congr 1
  calc
    (∫⁻ a : ℝ, localVarianceMass (μ.map (fun x ↦ -x)) a r) =
        ∫⁻ a : ℝ, localVarianceMass μ (-a - r) r := by
      apply lintegral_congr_ae
      filter_upwards [hleft, hright] with a ha hb
      exact localVarianceMass_map_neg_of_no_atoms μ a r ha hb
    _ = ∫⁻ a : ℝ, localVarianceMass μ a r := by
      have heq (a : ℝ) : -a - r = -r - a := by ring
      simp_rw [heq]
      exact lintegral_sub_left_eq_self (fun a : ℝ ↦ localVarianceMass μ a r) (-r)

lemma energyBelow_map_neg (μ : Measure ℝ) [SFinite μ] (R : ℝ) :
    energyBelow (μ.map (fun x ↦ -x)) R = energyBelow μ R := by
  simp only [energyBelow, normalizedLocalVariance_map_neg]

lemma energy_map_neg (μ : Measure ℝ) [SFinite μ] :
    energy (μ.map (fun x ↦ -x)) = energy μ := by
  simp only [energy, normalizedLocalVariance_map_neg]

end ExactOverlaps.VarianceEnergy
