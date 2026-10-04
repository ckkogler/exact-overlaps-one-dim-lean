/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.ScaleEntropy.EntropyRecoding

/-!
# Conditional-entropy Jensen on countable alphabets

A finitely supported mixture forces almost every component onto its finite
support. Retraction onto that support reduces integral Jensen to a genuinely
finite alphabet, while allowing exceptional components on a null set.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ENNReal Classical

namespace ExactOverlaps.ProbabilityVectors

open Entropy

lemma pmf_map_congr_on_support {α β : Type*} (p : PMF α) (f g : α → β)
    (h : ∀ a ∈ p.support, f a = g a) : p.map f = p.map g := by
  ext b
  simp only [PMF.map_apply]
  apply tsum_congr
  intro a
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · have hz : p a = 0 := by simpa using ha
    simp [hz]

lemma measurable_pmf_map {Ω α β : Type*} [MeasurableSpace Ω] [Countable α]
    (q : Ω → PMF α) (hq : ∀ a, Measurable (fun ω ↦ q ω a))
    (f : α → β) (b : β) : Measurable (fun ω ↦ (q ω).map f b) := by
  simp only [PMF.map_apply]
  apply Measurable.tsum
  intro a
  by_cases h : b = f a <;> simp only [h, ite_true, ite_false]
  · exact hq a
  · exact measurable_const

lemma pmf_map_mixture {Ω α β : Type*} [MeasurableSpace Ω] [Countable α]
    (θ : Measure Ω) (q : Ω → PMF α)
    (hq : ∀ a, Measurable (fun ω ↦ q ω a)) (p : PMF α)
    (hmix : ∀ a, p a = ∫⁻ ω, q ω a ∂θ) (f : α → β) (b : β) :
    p.map f b = ∫⁻ ω, (q ω).map f b ∂θ := by
  simp only [PMF.map_apply]
  rw [lintegral_tsum]
  · apply tsum_congr
    intro a
    by_cases h : b = f a <;> simp [h, hmix a]
  · intro a
    by_cases h : b = f a <;> simp only [h, ite_true, ite_false]
    · exact (hq a).aemeasurable
    · exact aemeasurable_const

lemma ae_support_subset_of_mixture {Ω α : Type*} [MeasurableSpace Ω] [Countable α]
    (θ : Measure Ω) (q : Ω → PMF α)
    (hq : ∀ a, Measurable (fun ω ↦ q ω a)) (p : PMF α)
    (hmix : ∀ a, p a = ∫⁻ ω, q ω a ∂θ) :
    ∀ᵐ ω ∂θ, (q ω).support ⊆ p.support := by
  have hz (a : α) : ∀ᵐ ω ∂θ, q ω a ≠ 0 → p a ≠ 0 := by
    by_cases ha : p a = 0
    · have hqa : ∀ᵐ ω ∂θ, q ω a = 0 :=
        (lintegral_eq_zero_iff (hq a)).mp ((hmix a).symm.trans ha)
      filter_upwards [hqa] with ω hω using fun h ↦ (h hω).elim
    · exact Filter.Eventually.of_forall (fun _ _ ↦ ha)
  exact (ae_all_iff.mpr hz).mono (fun _ h ↦ h)

/-- Jensen for finite-support laws on any countable fine alphabet. -/
theorem integral_conditionalEntropy_le_countable {Ω α β : Type*}
    [MeasurableSpace Ω] [Countable α] (θ : Measure Ω) [IsProbabilityMeasure θ]
    (q : Ω → PMF α) (hq : ∀ a, Measurable (fun ω ↦ q ω a))
    (hqfin : ∀ ω, (q ω).support.Finite) (p : PMF α) (hp : p.support.Finite)
    (hmix : ∀ a, p a = ∫⁻ ω, q ω a ∂θ) (f : α → β) :
    (∫ ω, conditionalEntropy (q ω) (hqfin ω) f ∂θ) ≤ conditionalEntropy p hp f := by
  let : Fintype p.support := hp.fintype
  obtain ⟨a₀, ha₀⟩ := p.support_nonempty
  let R : α → p.support := fun a ↦ if ha : a ∈ p.support then ⟨a, ha⟩ else ⟨a₀, ha₀⟩
  have hR (a : α) (ha : a ∈ p.support) : (R a).val = a := by
    dsimp only [R]
    rw [dite_eq_left ha]
  have hdecode (u : PMF α) (hu : u.support ⊆ p.support) :
      (u.map R).map Subtype.val = u := by
    rw [PMF.map_comp]
    calc
      u.map (Subtype.val ∘ R) = u.map id :=
        pmf_map_congr_on_support u _ _ (fun a ha ↦ hR a (hu ha))
      _ = u := PMF.map_id u
  have hcond (u : PMF α) (hufin : u.support.Finite) (hu : u.support ⊆ p.support) :
      conditionalEntropy (u.map R) (Set.toFinite _) (f ∘ Subtype.val) =
        conditionalEntropy u hufin f := by
    have h := conditionalEntropy_map_injective (u.map R) (Set.toFinite _)
      (g := fun a : p.support ↦ a.val) Subtype.val_injective f
    simpa only [hdecode u hu] using h.symm
  have hj := integral_conditionalEntropy_le_arbitrary θ (fun ω ↦ (q ω).map R)
    (measurable_pmf_map q hq R) (p.map R) (pmf_map_mixture θ q hq p hmix R)
    (f ∘ Subtype.val)
  rw [hcond p hp (Set.Subset.refl _)] at hj
  have he : (fun ω ↦ conditionalEntropy ((q ω).map R) (Set.toFinite _)
      (f ∘ Subtype.val)) =ᵐ[θ] (fun ω ↦ conditionalEntropy (q ω) (hqfin ω) f) :=
    (ae_support_subset_of_mixture θ q hq p hmix).mono
      (fun ω hω ↦ hcond (q ω) (hqfin ω) hω)
  rwa [integral_congr_ae he] at hj

end ExactOverlaps.ProbabilityVectors
