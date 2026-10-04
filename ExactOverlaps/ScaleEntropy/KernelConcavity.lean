/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.ScaleEntropy.FiniteSupportJensen
public import ExactOverlaps.ScaleEntropy.KernelIntegrability

/-!
# Scale-entropy concavity for arbitrary measurable mixtures

The mixture is the actual composition of a Markov kernel with its probability
mixing measure. Conditional-entropy Jensen applies to the quantized cell laws;
proved joint integrability permits averaging over a common translation period.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace ExactOverlaps.ScaleEntropy

open Entropy

variable {Ω : Type*} [MeasurableSpace Ω]

lemma integral_scaleConditional_le (κ : Kernel Ω ℝ) [IsMarkovKernel κ]
    (θ : Measure Ω) [IsProbabilityMeasure θ]
    (hκ : ∀ ω, HasBoundedSupport (componentLaw κ ω))
    (hμ : HasBoundedSupport (mixtureLaw κ θ))
    (r : ℝ) (hr : 0 < r) (C : ℕ) (t : ℝ) :
    (∫ ω, conditionalEntropy (law (componentLaw κ ω) r t)
      (law_support_finite _ (hκ ω) hr t) (fun k : ℤ ↦ k / (C : ℤ)) ∂θ) ≤
        conditionalEntropy (law (mixtureLaw κ θ) r t)
          (law_support_finite _ hμ hr t) (fun k : ℤ ↦ k / (C : ℤ)) := by
  exact ProbabilityVectors.integral_conditionalEntropy_le_countable θ
    (fun ω ↦ law (componentLaw κ ω) r t) (measurable_component_law_apply κ r t)
    (fun ω ↦ law_support_finite _ (hκ ω) hr t) _
    (law_support_finite _ hμ hr t) (law_mixture_apply κ θ r t) _

/-- Concavity between integer-related scales for arbitrary probability mixtures. -/
theorem entropyBetween_kernel_mixture_le (κ : Kernel Ω ℝ) [IsMarkovKernel κ]
    (θ : Measure Ω) [IsProbabilityMeasure θ]
    (hκ : ∀ ω, HasBoundedSupport (componentLaw κ ω))
    (hμ : HasBoundedSupport (mixtureLaw κ θ))
    (r : ℝ) (hr : 0 < r) (C : ℕ) (hC : 0 < C) :
    (∫ ω, entropyBetween (componentLaw κ ω) (hκ ω)
      r hr ((C : ℝ) * r) (mul_pos (Nat.cast_pos.mpr hC) hr) ∂θ) ≤
        entropyBetween (mixtureLaw κ θ) hμ
          r hr ((C : ℝ) * r) (mul_pos (Nat.cast_pos.mpr hC) hr) := by
  have hR : 0 < (C : ℝ) * r := mul_pos (Nat.cast_pos.mpr hC) hr
  have hi := integrable_component_scaleConditional_prod κ θ hκ hμ r hr C hC 0 ((C : ℝ) * r)
  have htarget := (intervalIntegrable_scaleConditional (mixtureLaw κ θ) hμ
    r hr C hC 0 ((C : ℝ) * r)).1
  have h := integral_mono hi.integral_prod_right htarget
    (fun t ↦ integral_scaleConditional_le κ θ hκ hμ r hr C t)
  have hswap := integral_integral_swap
    (f := fun ω t ↦ conditionalEntropy (law (componentLaw κ ω) r t)
      (law_support_finite _ (hκ ω) hr t) (fun k : ℤ ↦ k / (C : ℤ))) hi
  have hd := div_le_div_of_nonneg_right h hR.le
  simp_rw [entropyBetween_nat_mul_eq_conditional _ _ r hr C hC,
    intervalIntegral.integral_of_le hR.le]
  rw [integral_div, hswap]
  exact hd

end ExactOverlaps.ScaleEntropy
