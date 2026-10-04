module

public import ExactOverlaps.VarianceEnergy.IntervalMass
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Measurability of local variance

The squared error depends continuously on its center. The infimum over centers
is therefore measurable by separability of the real line. This justifies the
integrals defining local variance and variance energy for arbitrary finite laws.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace ExactOverlaps.VarianceEnergy

lemma localQuadraticError_eq_ofReal_integral (μ : Measure ℝ) [IsFiniteMeasure μ]
    (a r c : ℝ) : localQuadraticError μ a r c =
      ENNReal.ofReal (∫ x in Ico a (a + r), (x - c) ^ 2 ∂μ) := by
  symm
  apply ofReal_integral_eq_lintegral_ofReal
  · exact (((continuous_id.sub continuous_const).pow 2).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ico_subset_Icc_self
  · exact Filter.Eventually.of_forall (fun x ↦ sq_nonneg (x - c))

lemma continuous_localQuadraticError_center (μ : Measure ℝ) [IsFiniteMeasure μ]
    (a r : ℝ) : Continuous (fun c ↦ localQuadraticError μ a r c) := by
  have hcont : Continuous (fun c : ℝ ↦
      ∫ x in Icc a (a + r), (x - c) ^ 2 ∂μ.restrict (Ico a (a + r))) :=
    continuous_parametric_integral_of_continuous (by fun_prop) isCompact_Icc
  have heq : (fun c : ℝ ↦
      ∫ x in Icc a (a + r), (x - c) ^ 2 ∂μ.restrict (Ico a (a + r))) =
        (fun c : ℝ ↦ ∫ x in Ico a (a + r), (x - c) ^ 2 ∂μ) := by
    funext c
    rw [Measure.restrict_restrict measurableSet_Icc,
      inter_eq_right.mpr Ico_subset_Icc_self]
  rw [heq] at hcont
  simpa only [localQuadraticError_eq_ofReal_integral, Function.comp_def] using
    ENNReal.continuous_ofReal.comp hcont

lemma measurable_localQuadraticError (μ : Measure ℝ) [SFinite μ] (c : ℝ) :
    Measurable (fun p : ℝ × ℝ ↦ localQuadraticError μ p.1 p.2 c) := by
  classical
  let f : (ℝ × ℝ) → ℝ → ℝ≥0∞ := fun p x ↦
    if x ∈ Ico p.1 (p.1 + p.2) then ENNReal.ofReal ((x - c) ^ 2) else 0
  have hf : Measurable (Function.uncurry f) := by
    apply Measurable.ite _ _ measurable_const
    · exact (measurableSet_le measurable_fst.fst measurable_snd).inter
        (measurableSet_lt measurable_snd (measurable_fst.fst.add measurable_fst.snd))
    · fun_prop
  have heq : (fun p : ℝ × ℝ ↦ localQuadraticError μ p.1 p.2 c) =
      (fun p ↦ ∫⁻ x, f p x ∂μ) := by
    funext p
    rw [localQuadraticError, ← lintegral_indicator measurableSet_Ico]
    congr 1
    funext x
    simp only [f, Set.indicator_apply]
  rw [heq]
  exact hf.lintegral_prod_right

lemma measurable_localVarianceMass (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Measurable (fun p : ℝ × ℝ ↦ localVarianceMass μ p.1 p.2) := by
  have h := measurable_iInf_of_upperSemicontinuous
    (fun c ↦ measurable_localQuadraticError μ c)
    (fun p ↦ (continuous_localQuadraticError_center μ p.1 p.2).upperSemicontinuous)
  have heq : (⨅ c, fun p : ℝ × ℝ ↦ localQuadraticError μ p.1 p.2 c) =
      (fun p ↦ localVarianceMass μ p.1 p.2) := by
    funext p
    simp only [iInf_apply, localVarianceMass]
  rw [← heq]
  exact h

lemma measurable_normalizedLocalVariance (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Measurable (normalizedLocalVariance μ) := by
  have hf : Measurable (fun p : ℝ × ℝ ↦ localVarianceMass μ p.2 p.1) :=
    (measurable_localVarianceMass μ).comp measurable_swap
  have hi : Measurable (fun r : ℝ ↦ ∫⁻ a : ℝ, localVarianceMass μ a r) :=
    hf.lintegral_prod_right
  exact (by fun_prop : Measurable (fun r : ℝ ↦ ENNReal.ofReal (4 / r ^ 3))).mul hi

end ExactOverlaps.VarianceEnergy
