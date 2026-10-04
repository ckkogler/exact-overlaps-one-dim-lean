/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.ScaleEntropy.ConditionalJensen
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Conditional-entropy Jensen for actual finite-label probability laws

The component probability masses are measurable functions of an arbitrary
mixing parameter. Identifying their coordinatewise integrals with the target
law transfers vector Jensen to ordinary conditional Shannon entropy.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ENNReal Classical

namespace ExactOverlaps.ProbabilityVectors

open Entropy

variable {Ω α β : Type*} [MeasurableSpace Ω] [Fintype α] [Fintype β]

omit [Fintype α] in
lemma measurable_vectorOfPMF (q : Ω → PMF α)
    (hq : ∀ a, Measurable (fun ω ↦ q ω a)) :
    Measurable (fun ω ↦ vectorOfPMF (q ω)) :=
  Measurable.of_eval (fun a ↦ (hq a).ennreal_toReal)

/-- Integral Jensen for conditional entropy of actual finite-label laws. -/
theorem integral_conditionalEntropy_le (θ : Measure Ω) [IsProbabilityMeasure θ]
    (q : Ω → PMF α) (hq : ∀ a, Measurable (fun ω ↦ q ω a)) (p : PMF α)
    (hmix : ∀ a, (p a).toReal = ∫ ω, (q ω a).toReal ∂θ) (f : α → β) :
    (∫ ω, conditionalEntropy (q ω) (Set.toFinite _) f ∂θ) ≤
      conditionalEntropy p (Set.toFinite _) f := by
  have hm := measurable_vectorOfPMF q hq
  have hp : ∀ᵐ ω ∂θ, vectorOfPMF (q ω) ∈ simplex α :=
    Filter.Eventually.of_forall (fun ω ↦ vectorOfPMF_mem_simplex (q ω))
  have hi := integrable_probabilityVector θ (fun ω ↦ vectorOfPMF (q ω)) hm hp
  have he : (∫ ω, vectorOfPMF (q ω) ∂θ) = vectorOfPMF p := by
    funext a
    rw [eval_integral (fun a ↦ hi.eval a)]
    exact (hmix a).symm
  have h := integral_conditionalVector_le θ f (fun ω ↦ vectorOfPMF (q ω)) hm hp
  rw [he] at h
  simpa only [conditionalVector_vectorOfPMF] using h

/-- The same mixture theorem with its probability identity in ENNReal. -/
theorem integral_conditionalEntropy_le_of_lintegral (θ : Measure Ω) [IsProbabilityMeasure θ]
    (q : Ω → PMF α) (hq : ∀ a, Measurable (fun ω ↦ q ω a)) (p : PMF α)
    (hmix : ∀ a, p a = ∫⁻ ω, q ω a ∂θ) (f : α → β) :
    (∫ ω, conditionalEntropy (q ω) (Set.toFinite _) f ∂θ) ≤
      conditionalEntropy p (Set.toFinite _) f := by
  apply integral_conditionalEntropy_le θ q hq p _ f
  intro a
  rw [integral_toReal (hq a).aemeasurable
    (Filter.Eventually.of_forall (fun ω ↦ (q ω).apply_ne_top a |>.lt_top)), ← hmix a]

end ExactOverlaps.ProbabilityVectors
