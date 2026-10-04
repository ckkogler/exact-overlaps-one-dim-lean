/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.ScaleEntropy.Averaged
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.Kernel.MeasurableLIntegral

/-!
# Shifted cell laws of measurable probability kernels

The mixing parameter and physical grid translation vary jointly. Quantized
mixture masses are the integrals of the actual component masses.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace ExactOverlaps.ScaleEntropy

open Entropy

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The Borel probability measure at a parameter of a Markov kernel. -/
def componentLaw (κ : Kernel Ω ℝ) [IsMarkovKernel κ] (ω : Ω) : ProbabilityMeasure ℝ :=
  ⟨κ ω, inferInstance⟩

/-- The actual probability mixture, with no restriction on the mixing space. -/
def mixtureLaw (κ : Kernel Ω ℝ) [IsMarkovKernel κ]
    (θ : Measure Ω) [IsProbabilityMeasure θ] : ProbabilityMeasure ℝ :=
  ⟨κ ∘ₘ θ, inferInstance⟩

lemma law_mixture_apply (κ : Kernel Ω ℝ) [IsMarkovKernel κ]
    (θ : Measure Ω) [IsProbabilityMeasure θ] (r t : ℝ) (k : ℤ) :
    law (mixtureLaw κ θ) r t k = ∫⁻ ω, law (componentLaw κ ω) r t k ∂θ := by
  simp_rw [law_apply]
  change (κ ∘ₘ θ) {x | quantize r t x = k} = ∫⁻ ω, κ ω {x | quantize r t x = k} ∂θ
  exact Measure.bind_apply ((measurable_quantize r t) (measurableSet_singleton k))
    κ.aemeasurable

@[fun_prop] lemma measurable_component_law_apply (κ : Kernel Ω ℝ) [IsMarkovKernel κ]
    (r t : ℝ) (k : ℤ) : Measurable (fun ω ↦ law (componentLaw κ ω) r t k) := by
  simp_rw [law_apply]
  change Measurable (fun ω ↦ κ ω {x | quantize r t x = k})
  exact κ.measurable_coe ((measurable_quantize r t) (measurableSet_singleton k))

@[fun_prop] lemma measurable_component_law_apply_joint (κ : Kernel Ω ℝ) [IsMarkovKernel κ]
    (r : ℝ) (k : ℤ) :
    Measurable (fun p : Ω × ℝ ↦ law (componentLaw κ p.1) r p.2 k) := by
  have hs : MeasurableSet {p : (Ω × ℝ) × ℝ | quantize r p.1.2 p.2 = k} :=
    ((measurable_quantize_joint r).comp (measurable_fst.snd.prodMk measurable_snd))
      (measurableSet_singleton k)
  simp_rw [law_apply]
  change Measurable (fun p : Ω × ℝ ↦ κ p.1 {x | quantize r p.2 x = k})
  simpa only [Kernel.prodMkRight_apply,
    Set.preimage_ofPred_eq] using
    (Kernel.measurable_kernel_prodMk_left (κ := Kernel.prodMkRight ℝ κ) hs)

@[fun_prop] lemma measurable_component_shiftedEntropy_joint
    (κ : Kernel Ω ℝ) [IsMarkovKernel κ]
    (hκ : ∀ ω, HasBoundedSupport (componentLaw κ ω)) (r : ℝ) (hr : 0 < r) :
    Measurable (fun p : Ω × ℝ ↦ shiftedEntropy (componentLaw κ p.1) (hκ p.1) r hr p.2) := by
  simp only [shiftedEntropy_eq_tsum]
  exact Measurable.tsum (fun k ↦ Real.continuous_negMulLog.measurable.comp
    (measurable_component_law_apply_joint κ r k).ennreal_toReal)

lemma ae_component_support_interval (κ : Kernel Ω ℝ) [IsMarkovKernel κ]
    (θ : Measure Ω) [IsProbabilityMeasure θ] {a b : ℝ}
    (h : ∀ᵐ x ∂(mixtureLaw κ θ : Measure ℝ), x ∈ Icc a b) :
    ∀ᵐ ω ∂θ, ∀ᵐ x ∂(componentLaw κ ω : Measure ℝ), x ∈ Icc a b :=
  Measure.ae_ae_of_ae_comp h

end ExactOverlaps.ScaleEntropy
