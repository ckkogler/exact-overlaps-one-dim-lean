/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.ScaleEntropy.KernelLaws
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integrability of entropy over parameters and translations

Bounded support of the actual mixture gives a common support interval for
almost every component. A fixed finite label bound on every compact shift
interval then justifies Fubini, including arbitrary null exceptional components.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace ExactOverlaps.ScaleEntropy

open Entropy

variable {Ω : Type*} [MeasurableSpace Ω]

lemma integrable_component_shiftedEntropy_prod (κ : Kernel Ω ℝ) [IsMarkovKernel κ]
    (θ : Measure Ω) [IsProbabilityMeasure θ]
    (hκ : ∀ ω, HasBoundedSupport (componentLaw κ ω))
    (hμ : HasBoundedSupport (mixtureLaw κ θ)) (r : ℝ) (hr : 0 < r) (u v : ℝ) :
    Integrable (fun p : Ω × ℝ ↦ shiftedEntropy (componentLaw κ p.1) (hκ p.1) r hr p.2)
      (θ.prod (volume.restrict (Ioc u v))) := by
  obtain ⟨a, b, hab⟩ := hμ
  have hm := measurable_component_shiftedEntropy_joint κ hκ r hr
  apply Integrable.of_bound hm.aestronglyMeasurable
    ((Finset.Icc (quantize r u a) (quantize r v b)).card : ℝ)
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hm.norm measurable_const)).mpr
  filter_upwards [ae_component_support_interval κ θ hab] with ω hω
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (shiftedEntropy_nonneg _ _ _ _ _)]
  exact shiftedEntropy_le_uniform_card (componentLaw κ ω) (hκ ω) hr hω ⟨ht.1.le, ht.2⟩

lemma measurable_component_scaleConditional_joint (κ : Kernel Ω ℝ) [IsMarkovKernel κ]
    (hκ : ∀ ω, HasBoundedSupport (componentLaw κ ω))
    (r : ℝ) (hr : 0 < r) (C : ℕ) (hC : 0 < C) :
    Measurable (fun p : Ω × ℝ ↦ conditionalEntropy (law (componentLaw κ p.1) r p.2)
      (law_support_finite _ (hκ p.1) hr p.2) (fun k : ℤ ↦ k / (C : ℤ))) := by
  convert (measurable_component_shiftedEntropy_joint κ hκ r hr).sub
    (measurable_component_shiftedEntropy_joint κ hκ _
      (mul_pos (Nat.cast_pos.mpr hC) hr)) using 1
  funext p
  exact (shiftedEntropy_sub_eq_conditional (componentLaw κ p.1) (hκ p.1) r hr C hC p.2).symm

lemma integrable_component_scaleConditional_prod (κ : Kernel Ω ℝ) [IsMarkovKernel κ]
    (θ : Measure Ω) [IsProbabilityMeasure θ]
    (hκ : ∀ ω, HasBoundedSupport (componentLaw κ ω))
    (hμ : HasBoundedSupport (mixtureLaw κ θ))
    (r : ℝ) (hr : 0 < r) (C : ℕ) (hC : 0 < C) (u v : ℝ) :
    Integrable (fun p : Ω × ℝ ↦ conditionalEntropy (law (componentLaw κ p.1) r p.2)
      (law_support_finite _ (hκ p.1) hr p.2) (fun k : ℤ ↦ k / (C : ℤ)))
      (θ.prod (volume.restrict (Ioc u v))) := by
  convert (integrable_component_shiftedEntropy_prod κ θ hκ hμ r hr u v).sub
    (integrable_component_shiftedEntropy_prod κ θ hκ hμ _
      (mul_pos (Nat.cast_pos.mpr hC) hr) u v) using 1
  funext p
  exact (shiftedEntropy_sub_eq_conditional (componentLaw κ p.1) (hκ p.1) r hr C hC p.2).symm

lemma integrable_component_entropyBetween (κ : Kernel Ω ℝ) [IsMarkovKernel κ]
    (θ : Measure Ω) [IsProbabilityMeasure θ]
    (hκ : ∀ ω, HasBoundedSupport (componentLaw κ ω))
    (hμ : HasBoundedSupport (mixtureLaw κ θ))
    (r : ℝ) (hr : 0 < r) (C : ℕ) (hC : 0 < C) :
    Integrable (fun ω ↦ entropyBetween (componentLaw κ ω) (hκ ω)
      r hr ((C : ℝ) * r) (mul_pos (Nat.cast_pos.mpr hC) hr)) θ := by
  simp_rw [entropyBetween_nat_mul_eq_conditional _ _ r hr C hC,
    intervalIntegral.integral_of_le (mul_pos (Nat.cast_pos.mpr hC) hr).le]
  exact (integrable_component_scaleConditional_prod κ θ hκ hμ r hr C hC 0
    ((C : ℝ) * r)).integral_prod_left.div_const _

end ExactOverlaps.ScaleEntropy
