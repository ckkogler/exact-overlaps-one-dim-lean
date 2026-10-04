/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.ConvolutionDisintegration.FamilyRepresentation
public import ExactOverlaps.ScaleEntropy.KernelConcavity

/-!
The genuine kernel-mixture entropy inequality applied to measurable
convolution families, with integrable exponential cost. All integrals
are finite ordinary integrals under the actual probability mixing law.
-/

@[expose] public section

noncomputable section
open MeasureTheory

namespace ExactOverlaps.WFullDimension

open ConvolutionDisintegration Entropy ScaleEntropy

variable {I : Type*} [MeasurableSpace I]

lemma integrable_family_cost (θ : ProbabilityMeasure I)
    (f : I → FactorFamily) (hf : Measurable f) (s : ℝ) :
    Integrable (fun i ↦ cost s (f i)) (θ : Measure I) := by
  apply Integrable.of_bound ((measurable_cost s).comp hf).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun i ↦ by
    change ‖cost s (f i)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_pos (cost_pos _ _)]
    exact cost_le_one _ _)

theorem family_entropy_lower_bound (θ : ProbabilityMeasure I)
    (f : I → FactorFamily) (hf : Measurable f)
    (hF : ∀ i, HasBoundedSupport (convolutionLaw (f i)))
    (hμ : HasBoundedSupport (familyMixture θ f hf))
    (r : ℝ) (hr : 0 < r) (s L K : ℝ)
    (hbound : ∀ i, L * (1 - K * cost s (f i)) ≤
      entropyBetween (convolutionLaw (f i)) (hF i) r hr (2 * r) (by positivity)) :
    L * (1 - K * ∫ i, cost s (f i) ∂(θ : Measure I)) ≤
      entropyBetween (familyMixture θ f hf) hμ r hr (2 * r) (by positivity) := by
  have hcomp : ∀ i, HasBoundedSupport (componentLaw (familyKernel f hf) i) := hF
  have hmix : HasBoundedSupport (mixtureLaw (familyKernel f hf) (θ : Measure I)) := hμ
  have hi := integrable_component_entropyBetween (familyKernel f hf) (θ : Measure I)
    hcomp hmix r hr 2 (by norm_num)
  have hj := entropyBetween_kernel_mixture_le (familyKernel f hf) (θ : Measure I)
    hcomp hmix r hr 2 (by norm_num)
  norm_num only [Nat.cast_ofNat] at hi hj
  have hcost := integrable_family_cost θ f hf s
  have hl : Integrable (fun i ↦ L * (1 - K * cost s (f i))) (θ : Measure I) :=
    ((integrable_const (1 : ℝ)).sub (hcost.const_mul K)).const_mul L
  have hh := integral_mono hl hi hbound
  have he : (∫ i, L * (1 - K * cost s (f i)) ∂(θ : Measure I)) =
      L * (1 - K * ∫ i, cost s (f i) ∂(θ : Measure I)) := by
    rw [integral_const_mul, integral_sub (integrable_const (1 : ℝ)) (hcost.const_mul K),
      integral_const_mul]
    simp
  rw [he] at hh
  exact hh.trans hj

end ExactOverlaps.WFullDimension
