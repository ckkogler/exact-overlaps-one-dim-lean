module

public import ExactOverlaps.VarianceEnergy.Measurable
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Moments.Variance

/-!
# Ordinary conditional variance

For any finite real measure the window error is its window mass times the
ordinary variance under the normalized restriction. This proves the two
equivalent descriptions in the source definition, including zero-mass windows.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace ExactOverlaps.VarianceEnergy

lemma integral_sq_sub_eq_variance_add (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hx : MemLp (fun x : ℝ ↦ x) 2 ν) (c : ℝ) :
    (∫ x, (x - c) ^ 2 ∂ν) = ProbabilityTheory.variance (fun x : ℝ ↦ x) ν +
      ((∫ x, x ∂ν) - c) ^ 2 := by
  have hi : Integrable (fun x : ℝ ↦ x) ν := hx.integrable (by norm_num)
  have hfun : (fun x : ℝ ↦ (x - c) ^ 2) =
      (fun x : ℝ ↦ x ^ 2 - (2 * c) * x + c ^ 2) := by
    funext x
    ring
  have hquad : Integrable (fun x : ℝ ↦ x ^ 2 - (2 * c) * x) ν := by
    apply (hx.integrable_sq.sub (hi.const_mul (2 * c))).congr
    exact Filter.Eventually.of_forall (fun x ↦ by simp only [Pi.sub_apply])
  rw [hfun, integral_add hquad (integrable_const (c ^ 2)),
    integral_sub hx.integrable_sq (hi.const_mul (2 * c)), integral_const_mul,
    ProbabilityTheory.variance_eq_sub (μ := ν) hx]
  have huniv : ν.real univ = 1 := by simp
  simp only [Pi.pow_apply, integral_const, huniv, one_smul]
  ring

lemma iInf_lintegral_sq_sub_eq_variance (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hx : MemLp (fun x : ℝ ↦ x) 2 ν) :
    (⨅ c : ℝ, ∫⁻ x, ENNReal.ofReal ((x - c) ^ 2) ∂ν) =
      ENNReal.ofReal (ProbabilityTheory.variance (fun x : ℝ ↦ x) ν) := by
  have heq (c : ℝ) : (∫⁻ x, ENNReal.ofReal ((x - c) ^ 2) ∂ν) =
      ENNReal.ofReal (ProbabilityTheory.variance (fun x : ℝ ↦ x) ν +
        ((∫ x, x ∂ν) - c) ^ 2) := by
    have hsub : MemLp (fun x : ℝ ↦ x - c) 2 ν := hx.sub (memLp_const c)
    rw [← ofReal_integral_eq_lintegral_ofReal hsub.integrable_sq
      (Filter.Eventually.of_forall (fun x ↦ sq_nonneg (x - c))),
      integral_sq_sub_eq_variance_add ν hx]
  apply le_antisymm
  · calc
      (⨅ c : ℝ, ∫⁻ x, ENNReal.ofReal ((x - c) ^ 2) ∂ν) ≤
          ∫⁻ x, ENNReal.ofReal ((x - (∫ y, y ∂ν)) ^ 2) ∂ν := iInf_le _ _
      _ = _ := by rw [heq]; simp
  · apply le_iInf
    intro c
    rw [heq]
    exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (sq_nonneg _))

lemma memLp_id_cond_interval (μ : Measure ℝ) (a r : ℝ) :
    MemLp (fun x : ℝ ↦ x) 2 (ProbabilityTheory.cond μ (Ico a (a + r))) := by
  refine memLp_of_bounded (a := a) (b := a + r) ?_ measurable_id.aestronglyMeasurable 2
  filter_upwards [ProbabilityTheory.ae_cond_mem (μ := μ) measurableSet_Ico] with x hx
  exact ⟨hx.1, hx.2.le⟩

/-- The infimum definition is mass times ordinary variance of the conditional law. -/
lemma localVarianceMass_eq_cond_variance (μ : Measure ℝ) [IsFiniteMeasure μ]
    (a r : ℝ) : localVarianceMass μ a r = μ (Ico a (a + r)) *
      ENNReal.ofReal (ProbabilityTheory.variance (fun x : ℝ ↦ x)
        (ProbabilityTheory.cond μ (Ico a (a + r)))) := by
  by_cases hzero : μ (Ico a (a + r)) = 0
  · have hrestrict : μ.restrict (Ico a (a + r)) = 0 := Measure.restrict_eq_zero.mpr hzero
    simp [localVarianceMass, localQuadraticError, hrestrict, hzero]
  · have htop : μ (Ico a (a + r)) ≠ ∞ := measure_ne_top _ _
    let : IsProbabilityMeasure (ProbabilityTheory.cond μ (Ico a (a + r))) :=
      ProbabilityTheory.cond_isProbabilityMeasure hzero
    have hrestrict : μ.restrict (Ico a (a + r)) =
        μ (Ico a (a + r)) • ProbabilityTheory.cond μ (Ico a (a + r)) := by
      rw [ProbabilityTheory.cond, smul_smul, ENNReal.mul_inv_cancel hzero htop, one_smul]
    simp only [localVarianceMass, localQuadraticError, hrestrict, lintegral_smul_measure,
      smul_eq_mul]
    rw [← ENNReal.mul_iInf_of_ne hzero htop,
      iInf_lintegral_sq_sub_eq_variance _ (memLp_id_cond_interval μ a r)]

end ExactOverlaps.VarianceEnergy
