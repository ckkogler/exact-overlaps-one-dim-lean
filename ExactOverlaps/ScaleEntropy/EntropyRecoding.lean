/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.ScaleEntropy.PMFJensen

/-!
# Recoding finite conditional entropy

Injective fine or coarse recodings preserve conditional entropy. In particular,
the coarse alphabet of the finite-label integral Jensen theorem may be arbitrary:
only the range of its label map matters.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ENNReal Classical

namespace ExactOverlaps.ProbabilityVectors

open Entropy

lemma conditionalEntropy_map_injective {α β γ : Type*} (p : PMF α)
    (hp : p.support.Finite) {g : α → β} (hg : Function.Injective g) (f : β → γ) :
    conditionalEntropy (p.map g) (by simpa using hp.image g) f =
      conditionalEntropy p hp (f ∘ g) := by
  simp only [conditionalEntropy_eq_entropy_sub, PMF.map_comp,
    finiteEntropy_map_of_injective p hp hg]

lemma conditionalEntropy_coarse_injective {α β γ : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → β) {g : β → γ} (hg : Function.Injective g) :
    conditionalEntropy p hp (g ∘ f) = conditionalEntropy p hp f := by
  have he := finiteEntropy_map_of_injective (p.map f)
    (show (p.map f).support.Finite from by simpa using hp.image f) hg
  simpa only [conditionalEntropy_eq_entropy_sub, PMF.map_comp] using
    congrArg (fun z ↦ finiteEntropy p hp - z) he

lemma conditionalEntropy_rangeFactorization {α β : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → β) :
    conditionalEntropy p hp f = conditionalEntropy p hp (Set.rangeFactorization f) := by
  exact conditionalEntropy_coarse_injective p hp (Set.rangeFactorization f)
    (g := fun x : Set.range f ↦ x.val) Subtype.val_injective

/-- Jensen with an arbitrary coarse alphabet and finite fine alphabet. -/
theorem integral_conditionalEntropy_le_arbitrary {Ω α β : Type*}
    [MeasurableSpace Ω] [Fintype α] (θ : Measure Ω) [IsProbabilityMeasure θ]
    (q : Ω → PMF α) (hq : ∀ a, Measurable (fun ω ↦ q ω a)) (p : PMF α)
    (hmix : ∀ a, p a = ∫⁻ ω, q ω a ∂θ) (f : α → β) :
    (∫ ω, conditionalEntropy (q ω) (Set.toFinite _) f ∂θ) ≤
      conditionalEntropy p (Set.toFinite _) f := by
  let : Fintype (Set.range f) := (Set.finite_range f).fintype
  simpa only [conditionalEntropy_rangeFactorization _ _ f] using
    integral_conditionalEntropy_le_of_lintegral θ q hq p hmix (Set.rangeFactorization f)

end ExactOverlaps.ProbabilityVectors
