/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.ConvolutionDisintegration.FactorSpace
public import Mathlib.MeasureTheory.MeasurableSpace.Prod

/-!
# Products with countable measurable disjoint unions

Each disjoint-union injection is a measurable embedding. A function on a
product with a countable disjoint union is measurable when its restrictions
to the individual product fibers are measurable. This supports variable
factor counts without assuming measurability of concatenation.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set

namespace ExactOverlaps.ConvolutionDisintegration

lemma measurableEmbedding_sigma_injection {ι : Type*} {A : ι → Type*}
    [∀ i, MeasurableSpace (A i)] (i : ι) :
    MeasurableEmbedding (Sigma.mk i : A i → Sigma A) where
  injective := by intro x y h; simpa using h
  measurable := measurable_sigma_injection i
  measurableSet_image' := by
    intro E hE
    change MeasurableSet[⨅ j, (inferInstance : MeasurableSpace (A j)).map (Sigma.mk j)] _
    rw [MeasurableSpace.measurableSet_iInf]
    intro j
    change MeasurableSet ((Sigma.mk j) ⁻¹' (Sigma.mk i '' E))
    by_cases hij : i = j
    · subst j
      have hinj : Function.Injective (Sigma.mk i : A i → Sigma A) :=
        fun x y h ↦ by simpa using h
      simpa only [hinj.preimage_image] using hE
    · have he : (Sigma.mk j) ⁻¹' (Sigma.mk i '' E) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        rintro x ⟨y, _, h⟩
        exact hij (congrArg Sigma.fst h)
      rw [he]
      exact MeasurableSet.empty

lemma measurable_from_prod_sigma {ι : Type*} [Countable ι] {A : ι → Type*}
    [∀ i, MeasurableSpace (A i)] {B C : Type*} [MeasurableSpace B] [MeasurableSpace C]
    (f : B × Sigma A → C)
    (hf : ∀ i, Measurable (fun p : B × A i ↦ f (p.1, ⟨i, p.2⟩))) : Measurable f := by
  intro E hE
  have he : f ⁻¹' E = ⋃ i, (Prod.map id (Sigma.mk i)) ''
      ((fun p : B × A i ↦ f (p.1, ⟨i, p.2⟩)) ⁻¹' E) := by
    ext p
    constructor
    · intro hp
      exact mem_iUnion.mpr ⟨p.2.1, ⟨(p.1, p.2.2), hp, rfl⟩⟩
    · intro hp
      obtain ⟨i, q, hq, rfl⟩ := mem_iUnion.mp hp
      exact hq
  rw [he]
  exact MeasurableSet.iUnion (fun i ↦
    (MeasurableEmbedding.id.prodMap (measurableEmbedding_sigma_injection i)).measurableSet_image'
      (hf i hE))

lemma measurable_from_sigma_prod {ι : Type*} [Countable ι] {A : ι → Type*}
    [∀ i, MeasurableSpace (A i)] {B C : Type*} [MeasurableSpace B] [MeasurableSpace C]
    (f : Sigma A × B → C)
    (hf : ∀ i, Measurable (fun p : A i × B ↦ f (⟨i, p.1⟩, p.2))) : Measurable f := by
  have h := measurable_from_prod_sigma (fun p : B × Sigma A ↦ f (p.2, p.1))
    (fun i ↦ (hf i).comp measurable_swap)
  exact h.comp measurable_swap

end ExactOverlaps.ConvolutionDisintegration
