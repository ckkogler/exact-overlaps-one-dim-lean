/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.ConvolutionDisintegration.DiracRepresentation

/-!
# Everywhere admissible representatives

An almost everywhere admissible convolution family can be changed on its
inadmissible null set to the single Dirac factor at zero. The replacement
is measurable, is admissible at every index, and has exactly the same
convolution mixture and integrated cost. Thus the almost everywhere
convention in the canonical definition also realizes the literal
every-index formulation.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace ExactOverlaps.ConvolutionDisintegration

def admissibleReplacement (r : ℝ) (c : FactorFamily) : FactorFamily := by
  classical
  exact if Admissible r c then c else singleDirac 0

lemma measurable_admissibleReplacement (r : ℝ) : Measurable (admissibleReplacement r) := by
  classical
  exact measurable_id.ite (measurableSet_admissible r) measurable_const

lemma admissible_admissibleReplacement {r : ℝ} (hr : 0 ≤ r) (c : FactorFamily) :
    Admissible r (admissibleReplacement r c) := by
  classical
  unfold admissibleReplacement
  split_ifs with h
  · exact h
  · exact admissible_singleDirac hr 0

lemma admissibleReplacement_eq_self {r : ℝ} {c : FactorFamily} (h : Admissible r c) :
    admissibleReplacement r c = c := by
  classical
  exact ite_eq_left h

lemma admissibleReplacement_ae_eq {I : Type*} [MeasurableSpace I]
    {θ : Measure I} {f : I → FactorFamily} {r : ℝ}
    (h : ∀ᵐ i ∂θ, Admissible r (f i)) :
    (fun i ↦ admissibleReplacement r (f i)) =ᵐ[θ] f :=
  h.mono fun _ hi ↦ admissibleReplacement_eq_self hi

lemma familyMixture_congr_ae {I : Type*} [MeasurableSpace I]
    (θ : ProbabilityMeasure I) {f g : I → FactorFamily}
    (hf : Measurable f) (hg : Measurable g) (h : f =ᵐ[(θ : Measure I)] g) :
    familyMixture θ f hf = familyMixture θ g hg := by
  apply Subtype.ext
  apply Measure.bind_congr_right
  exact h.mono fun _ hi ↦ congrArg (fun c ↦ (convolutionLaw c : Measure ℝ)) hi

lemma familyMixture_admissibleReplacement {I : Type*} [MeasurableSpace I]
    (θ : ProbabilityMeasure I) (f : I → FactorFamily) (hf : Measurable f) {r : ℝ}
    (h : ∀ᵐ i ∂(θ : Measure I), Admissible r (f i)) :
    familyMixture θ (admissibleReplacement r ∘ f)
      ((measurable_admissibleReplacement r).comp hf) = familyMixture θ f hf := by
  exact familyMixture_congr_ae θ _ hf (admissibleReplacement_ae_eq h)

lemma familyCost_admissibleReplacement {I : Type*} [MeasurableSpace I]
    (θ : ProbabilityMeasure I) (f : I → FactorFamily) {r : ℝ}
    (h : ∀ᵐ i ∂(θ : Measure I), Admissible r (f i)) :
    (∫ i, cost r (admissibleReplacement r (f i)) ∂(θ : Measure I)) =
      ∫ i, cost r (f i) ∂(θ : Measure I) := by
  apply integral_congr_ae
  exact (admissibleReplacement_ae_eq h).mono fun _ hi ↦ congrArg (cost r) hi

theorem pointwise_family_representation {I : Type*} [MeasurableSpace I]
    {μ : ProbabilityMeasure ℝ} {r : ℝ} (hr : 0 ≤ r)
    (θ : ProbabilityMeasure I) (f : I → FactorFamily) (hf : Measurable f)
    (h : IsFamilyDisintegration μ r θ f hf) :
    ∃ g : I → FactorFamily, ∃ hg : Measurable g,
      (∀ i, Admissible r (g i)) ∧ familyMixture θ g hg = μ ∧
      (∫ i, cost r (g i) ∂(θ : Measure I)) = ∫ i, cost r (f i) ∂(θ : Measure I) := by
  refine ⟨admissibleReplacement r ∘ f, (measurable_admissibleReplacement r).comp hf,
    fun i ↦ admissible_admissibleReplacement hr (f i), ?_,
    familyCost_admissibleReplacement θ f h.2⟩
  exact (familyMixture_admissibleReplacement θ f hf h.2).trans h.1

theorem pointwise_canonical_representation {μ : ProbabilityMeasure ℝ} {r : ℝ}
    (hr : 0 ≤ r) (θ : ProbabilityMeasure FactorFamily) (h : IsDisintegration μ r θ) :
    ∃ f : FactorFamily → FactorFamily, ∃ hf : Measurable f,
      (∀ c, Admissible r (f c)) ∧ familyMixture θ f hf = μ ∧
      (∫ c, cost r (f c) ∂(θ : Measure FactorFamily)) = averageCost r θ := by
  exact pointwise_family_representation hr θ id measurable_id h

end ExactOverlaps.ConvolutionDisintegration
