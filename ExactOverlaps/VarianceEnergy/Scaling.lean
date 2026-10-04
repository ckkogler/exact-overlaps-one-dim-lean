module

public import ExactOverlaps.VarianceEnergy.Measurable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Positive scaling of local variance

Scaling a law by a positive factor scales squared error quadratically and
window origins linearly. The normalization leaves only the rescaled window.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace ExactOverlaps.VarianceEnergy

lemma localQuadraticError_map_mul_pos (μ : Measure ℝ) {u : ℝ} (hu : 0 < u)
    (a r c : ℝ) : localQuadraticError (μ.map (fun x ↦ u * x)) a r c =
      ENNReal.ofReal (u ^ 2) * localQuadraticError μ (a / u) (r / u) (c / u) := by
  have hpre : (fun x : ℝ ↦ u * x) ⁻¹' Ico a (a + r) =
      Ico (a / u) (a / u + r / u) := by
    ext x
    simp only [mem_preimage, mem_Ico, ← add_div, div_le_iff₀ hu, lt_div_iff₀ hu]
    simp only [mul_comm]
  unfold localQuadraticError
  rw [setLIntegral_map measurableSet_Ico (by fun_prop) (by fun_prop), hpre]
  calc
    (∫⁻ x in Ico (a / u) (a / u + r / u), ENNReal.ofReal ((u * x - c) ^ 2) ∂μ) =
        ∫⁻ x in Ico (a / u) (a / u + r / u),
          ENNReal.ofReal (u ^ 2) * ENNReal.ofReal ((x - c / u) ^ 2) ∂μ := by
      apply lintegral_congr
      intro x
      rw [← ENNReal.ofReal_mul (sq_nonneg u)]
      congr 1
      field_simp [ne_of_gt hu]
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

lemma localVarianceMass_map_mul_pos (μ : Measure ℝ) {u : ℝ} (hu : 0 < u)
    (a r : ℝ) : localVarianceMass (μ.map (fun x ↦ u * x)) a r =
      ENNReal.ofReal (u ^ 2) * localVarianceMass μ (a / u) (r / u) := by
  simp only [localVarianceMass, localQuadraticError_map_mul_pos μ hu]
  rw [← ENNReal.mul_iInf_of_ne (by positivity) ENNReal.ofReal_ne_top]
  congr 1
  have hsurj : Function.Surjective (fun c : ℝ ↦ c / u) := by
    intro x
    exact ⟨x * u, mul_div_cancel_right₀ x (ne_of_gt hu)⟩
  exact hsurj.iInf_comp (fun c ↦ localQuadraticError μ (a / u) (r / u) c)

lemma map_volume_div_pos {u : ℝ} (hu : 0 < u) :
    volume.map (fun x : ℝ ↦ x / u) = ENNReal.ofReal u • volume := by
  have hfun : (fun x : ℝ ↦ x / u) = (fun x : ℝ ↦ u⁻¹ * x) := by
    funext x
    rw [div_eq_mul_inv, mul_comm]
  rw [hfun, Real.map_volume_mul_left (inv_ne_zero (ne_of_gt hu)), inv_inv, abs_of_pos hu]

lemma lintegral_div_pos (f : ℝ → ℝ≥0∞) (hf : Measurable f) {u : ℝ} (hu : 0 < u) :
    (∫⁻ x : ℝ, f (x / u)) = ENNReal.ofReal u * ∫⁻ x : ℝ, f x := by
  rw [← lintegral_map hf (by fun_prop), map_volume_div_pos hu, lintegral_smul_measure]
  rfl

lemma normalizedLocalVariance_map_mul_pos (μ : Measure ℝ) [IsFiniteMeasure μ]
    {u r : ℝ} (hu : 0 < u) (hr : 0 < r) :
    normalizedLocalVariance (μ.map (fun x ↦ u * x)) r =
      normalizedLocalVariance μ (r / u) := by
  have hm : Measurable (fun a : ℝ ↦ localVarianceMass μ a (r / u)) :=
    (measurable_localVarianceMass μ).comp (measurable_id.prodMk measurable_const)
  have hfactor : ENNReal.ofReal (4 / r ^ 3) *
      (ENNReal.ofReal (u ^ 2) * ENNReal.ofReal u) =
        ENNReal.ofReal (4 / (r / u) ^ 3) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp [ne_of_gt hu, ne_of_gt hr]
  simp only [normalizedLocalVariance, localVarianceMass_map_mul_pos μ hu]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_div_pos _ hm hu]
  calc
    _ = (ENNReal.ofReal (4 / r ^ 3) * (ENNReal.ofReal (u ^ 2) * ENNReal.ofReal u)) *
        ∫⁻ a : ℝ, localVarianceMass μ a (r / u) := by ac_rfl
    _ = _ := by rw [hfactor]

end ExactOverlaps.VarianceEnergy
