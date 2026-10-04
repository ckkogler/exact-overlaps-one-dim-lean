module

public import ExactOverlaps.VarianceEnergy.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Group.LIntegral

/-!
# Translation invariance of variance energy

Translating a law translates the sliding window and its optimizing center.
Lebesgue integration over window origins then removes the translation.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace ExactOverlaps.VarianceEnergy

lemma localQuadraticError_map_add (μ : Measure ℝ) (b a r c : ℝ) :
    localQuadraticError (μ.map (fun x ↦ x + b)) a r c =
      localQuadraticError μ (a - b) r (c - b) := by
  have hpre : (fun x : ℝ ↦ x + b) ⁻¹' Ico a (a + r) =
      Ico (a - b) (a - b + r) := by
    ext x
    simp only [mem_preimage, mem_Ico]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  unfold localQuadraticError
  rw [setLIntegral_map measurableSet_Ico (by fun_prop) (by fun_prop), hpre]
  apply lintegral_congr
  intro x
  congr 1
  ring

lemma localVarianceMass_map_add (μ : Measure ℝ) (b a r : ℝ) :
    localVarianceMass (μ.map (fun x ↦ x + b)) a r =
      localVarianceMass μ (a - b) r := by
  simp only [localVarianceMass, localQuadraticError_map_add]
  have hsurj : Function.Surjective (fun c : ℝ ↦ c - b) := by
    intro x
    exact ⟨x + b, by ring⟩
  exact hsurj.iInf_comp (fun c ↦ localQuadraticError μ (a - b) r c)

lemma normalizedLocalVariance_map_add (μ : Measure ℝ) (b r : ℝ) :
    normalizedLocalVariance (μ.map (fun x ↦ x + b)) r = normalizedLocalVariance μ r := by
  simp only [normalizedLocalVariance, localVarianceMass_map_add, sub_eq_add_neg]
  congr 1
  exact lintegral_add_right_eq_self (fun a : ℝ ↦ localVarianceMass μ a r) (-b)

lemma energyBelow_map_add (μ : Measure ℝ) (b R : ℝ) :
    energyBelow (μ.map (fun x ↦ x + b)) R = energyBelow μ R := by
  simp only [energyBelow, normalizedLocalVariance_map_add]

lemma energy_map_add (μ : Measure ℝ) (b : ℝ) :
    energy (μ.map (fun x ↦ x + b)) = energy μ := by
  simp only [energy, normalizedLocalVariance_map_add]

end ExactOverlaps.VarianceEnergy
