module

public import ExactOverlaps.VarianceEnergy.EnergyScaling
public import ExactOverlaps.VarianceEnergy.Reflection

/-!
# Signed affine covariance and energy invariance

Every nonzero real scaling is allowed. Negative factors use the reflection
argument, including its explicit almost-everywhere treatment of endpoints.
-/

@[expose] public section

noncomputable section
open MeasureTheory

namespace ExactOverlaps.VarianceEnergy

lemma map_neg_then_neg_mul (μ : Measure ℝ) (u : ℝ) :
    (μ.map (fun x ↦ -x)).map (fun x ↦ (-u) * x) = μ.map (fun x ↦ u * x) := by
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  simp only [Function.comp_def, neg_mul_neg]

lemma map_mul_then_add (μ : Measure ℝ) (u b : ℝ) :
    (μ.map (fun x ↦ u * x)).map (fun x ↦ x + b) = μ.map (fun x ↦ u * x + b) := by
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

lemma normalizedLocalVariance_map_mul (μ : Measure ℝ) [IsFiniteMeasure μ]
    {u r : ℝ} (hu : u ≠ 0) (hr : 0 < r) :
    normalizedLocalVariance (μ.map (fun x ↦ u * x)) r =
      normalizedLocalVariance μ (r / |u|) := by
  rcases lt_or_gt_of_ne hu with hneg | hpos
  · have h := normalizedLocalVariance_map_mul_pos (μ.map (fun x ↦ -x))
      (neg_pos.mpr hneg) hr
    rw [map_neg_then_neg_mul, normalizedLocalVariance_map_neg] at h
    simpa only [abs_of_neg hneg] using h
  · simpa only [abs_of_pos hpos] using normalizedLocalVariance_map_mul_pos μ hpos hr

lemma energy_map_mul (μ : Measure ℝ) [IsFiniteMeasure μ] {u : ℝ} (hu : u ≠ 0) :
    energy (μ.map (fun x ↦ u * x)) = energy μ := by
  rcases lt_or_gt_of_ne hu with hneg | hpos
  · have h := energy_map_mul_pos (μ.map (fun x ↦ -x)) (neg_pos.mpr hneg)
    rw [map_neg_then_neg_mul, energy_map_neg] at h
    exact h
  · exact energy_map_mul_pos μ hpos

/-- The signed affine local-variance identity from Lemma 2.1. -/
lemma normalizedLocalVariance_map_affine (μ : Measure ℝ) [IsFiniteMeasure μ]
    {u r : ℝ} (hu : u ≠ 0) (hr : 0 < r) (b : ℝ) :
    normalizedLocalVariance (μ.map (fun x ↦ u * x + b)) r =
      normalizedLocalVariance μ (r / |u|) := by
  rw [← map_mul_then_add, normalizedLocalVariance_map_add,
    normalizedLocalVariance_map_mul μ hu hr]

/-- Full variance energy is invariant under every invertible real affine map. -/
lemma energy_map_affine (μ : Measure ℝ) [IsFiniteMeasure μ]
    {u : ℝ} (hu : u ≠ 0) (b : ℝ) :
    energy (μ.map (fun x ↦ u * x + b)) = energy μ := by
  rw [← map_mul_then_add, energy_map_add, energy_map_mul μ hu]

end ExactOverlaps.VarianceEnergy
