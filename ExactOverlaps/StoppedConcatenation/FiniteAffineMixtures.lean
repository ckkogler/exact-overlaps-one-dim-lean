/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.FiniteMixtures
public import ExactOverlaps.SelfSimilar.Similarity
public import ExactOverlaps.Entropy.ConditionalConcavity
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-! Finite affine mixtures are the exact pushforwards of independent product laws. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ExactOverlaps.ConvolutionDisintegration

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

theorem finite_affine_product_map [Fintype α] (p : PMF α)
    (μ : ProbabilityMeasure ℝ) (g : α → RealSimilarity) :
    (p.toMeasure.prod (μ : Measure ℝ)).map (fun z ↦ g z.1 z.2) =
      (finiteMix p (fun i ↦ μ.map (g i)) : Measure ℝ) := by
  have hm : Measurable (fun z : α × ℝ ↦ g z.1 z.2) :=
    measurable_from_prod_countable_right (fun i ↦ (g i).measurable)
  apply Measure.ext
  intro E hE
  rw [Measure.map_apply hm hE, Measure.prod_apply (hE.preimage hm), lintegral_fintype]
  change (∑ i, _) = (∑ i, p i • ((μ.map (g i)) : Measure ℝ)) E
  rw [Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [PMF.toMeasure_apply_singleton p i (measurableSet_singleton i),
    Measure.smul_apply, smul_eq_mul, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (g i).measurable hE]
  exact mul_comm _ _

theorem finite_support_affine_product_map [Countable α] (p : PMF α)
    (hp : p.support.Finite) (μ : ProbabilityMeasure ℝ) (g : α → RealSimilarity) :
    (p.toMeasure.prod (μ : Measure ℝ)).map (fun z ↦ g z.1 z.2) =
      (letI := hp.fintype
       (finiteMix (Entropy.supportLaw p) (fun i ↦ μ.map (g i)) : Measure ℝ)) := by
  let := hp.fintype
  have hsupport : (Entropy.supportLaw p).toMeasure.map Subtype.val = p.toMeasure := by
    rw [PMF.toMeasure_map _ _ measurable_subtype_coe, Entropy.supportLaw_map_val]
  have hm : Measurable (fun z : α × ℝ ↦ g z.1 z.2) :=
    measurable_from_prod_countable_right (fun i ↦ (g i).measurable)
  calc
    _ = (((Entropy.supportLaw p).toMeasure.map Subtype.val).prod
        ((μ : Measure ℝ).map id)).map (fun z ↦ g z.1 z.2) := by
      rw [hsupport, Measure.map_id]
    _ = ((Entropy.supportLaw p).toMeasure.prod (μ : Measure ℝ)).map
        (fun z : p.support × ℝ ↦ g z.1 z.2) := by
      rw [Measure.map_prod_map _ _ measurable_subtype_coe measurable_id,
        Measure.map_map hm (measurable_subtype_coe.prodMap measurable_id)]
      rfl
    _ = _ := finite_affine_product_map (Entropy.supportLaw p) μ (fun i ↦ g i)

end ExactOverlaps.ConvolutionDisintegration
