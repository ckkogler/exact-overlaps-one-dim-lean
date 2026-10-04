/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.ConvolutionDisintegration.Admissibility

/-!
# Arbitrary measurable mixing spaces

A measurable family with a variable positive finite number of factors may
be pushed forward to the canonical factor space. Its actual convolution
mixture, admissibility and integrated cost are preserved exactly. Conversely,
the canonical space itself is an allowed mixing space.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace ExactOverlaps.ConvolutionDisintegration

def familyKernel {I : Type*} [MeasurableSpace I]
    (f : I → FactorFamily) (hf : Measurable f) : Kernel I ℝ where
  toFun i := convolutionLaw (f i)
  measurable' := measurable_subtype_coe.comp (measurable_convolutionLaw.comp hf)

instance {I : Type*} [MeasurableSpace I] (f : I → FactorFamily) (hf : Measurable f) :
    IsMarkovKernel (familyKernel f hf) where
  isProbabilityMeasure i := inferInstanceAs
    (IsProbabilityMeasure (convolutionLaw (f i) : Measure ℝ))

def familyMixture {I : Type*} [MeasurableSpace I] (θ : ProbabilityMeasure I)
    (f : I → FactorFamily) (hf : Measurable f) : ProbabilityMeasure ℝ :=
  ⟨familyKernel f hf ∘ₘ (θ : Measure I), inferInstance⟩

def IsFamilyDisintegration {I : Type*} [MeasurableSpace I]
    (μ : ProbabilityMeasure ℝ) (r : ℝ) (θ : ProbabilityMeasure I)
    (f : I → FactorFamily) (hf : Measurable f) : Prop :=
  familyMixture θ f hf = μ ∧ ∀ᵐ i ∂(θ : Measure I), Admissible r (f i)

lemma mixture_map_eq {I : Type*} [MeasurableSpace I] (θ : ProbabilityMeasure I)
    (f : I → FactorFamily) (hf : Measurable f) :
    mixture (θ.map f) = familyMixture θ f hf := by
  apply Subtype.ext
  apply Measure.ext
  intro E hE
  change ((θ : Measure I).map f).bind convolutionKernel E =
    (θ : Measure I).bind (familyKernel f hf) E
  have hm : Measurable (fun c : FactorFamily ↦ convolutionKernel c E) :=
    (Measure.measurable_coe hE).comp convolutionKernel.measurable
  rw [Measure.bind_apply hE convolutionKernel.aemeasurable,
    Measure.bind_apply hE (familyKernel f hf).aemeasurable, lintegral_map hm hf]
  rfl

lemma averageCost_map_eq {I : Type*} [MeasurableSpace I] (θ : ProbabilityMeasure I)
    (f : I → FactorFamily) (hf : Measurable f) (r : ℝ) :
    averageCost r (θ.map f) = ∫ i, cost r (f i) ∂(θ : Measure I) := by
  exact integral_map hf.aemeasurable (measurable_cost r).aestronglyMeasurable

lemma isDisintegration_map_iff {I : Type*} [MeasurableSpace I]
    (μ : ProbabilityMeasure ℝ) (r : ℝ) (θ : ProbabilityMeasure I)
    (f : I → FactorFamily) (hf : Measurable f) :
    IsDisintegration μ r (θ.map f) ↔ IsFamilyDisintegration μ r θ f hf := by
  unfold IsDisintegration IsFamilyDisintegration
  rw [mixture_map_eq]
  change (_ ∧ ∀ᵐ c ∂((θ : Measure I).map f), Admissible r c) ↔ _
  rw [ae_map_iff hf.aemeasurable (measurableSet_admissible r)]

lemma canonical_familyMixture (θ : ProbabilityMeasure FactorFamily) :
    familyMixture θ id measurable_id = mixture θ := rfl

lemma canonical_familyDisintegration (μ : ProbabilityMeasure ℝ) (r : ℝ)
    (θ : ProbabilityMeasure FactorFamily) :
    IsFamilyDisintegration μ r θ id measurable_id ↔ IsDisintegration μ r θ := Iff.rfl

theorem W_le_familyCost {I : Type*} [MeasurableSpace I]
    {μ : ProbabilityMeasure ℝ} {r : ℝ} (θ : ProbabilityMeasure I)
    (f : I → FactorFamily) (hf : Measurable f)
    (h : IsFamilyDisintegration μ r θ f hf) :
    W μ r ≤ ∫ i, cost r (f i) ∂(θ : Measure I) := by
  rw [← averageCost_map_eq θ f hf r]
  exact W_le_averageCost ((isDisintegration_map_iff μ r θ f hf).mpr h)

end ExactOverlaps.ConvolutionDisintegration
