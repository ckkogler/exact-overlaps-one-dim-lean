/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.ScaleEntropy.ProbabilityVectors

/-!
# Conditional entropy under arbitrary measurable mixtures

Finite conditional-entropy concavity gives concavity on the real probability
simplex. Its continuity and boundedness then justify integral Jensen for
every probability mixing measure, with no finite-support restriction.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical

namespace ExactOverlaps.ProbabilityVectors

open Entropy

variable {α β : Type*} [Fintype α] [Fintype β]

lemma concaveOn_conditionalVector (f : α → β) :
    ConcaveOn ℝ (simplex α) (conditionalVector f) := by
  refine ⟨convex_simplex, ?_⟩
  intro x hx y hy a b ha hb hab
  let w : Bool → ℝ := fun i ↦ cond i a b
  have hw : w ∈ simplex Bool := by
    refine ⟨?_, ?_⟩
    · intro i
      cases i <;> assumption
    · simpa [w, Fintype.sum_bool, add_comm] using hab
  let p : PMF Bool := ofVector w hw
  let q : Bool → PMF α := fun i ↦ cond i (ofVector x hx) (ofVector y hy)
  have hmix : vectorOfPMF (p.bind q) = a • x + b • y := by
    funext c
    rw [vectorOfPMF, bind_toReal]
    simp only [Fintype.sum_bool, p, q, Bool.cond_false, Bool.cond_true, ofVector_toReal]
    simp [w, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h := average_conditionalEntropy_le_bind p q (fun _ ↦ Set.toFinite _) f
  simp only [← conditionalVector_vectorOfPMF, hmix, Fintype.sum_bool, p, q,
    Bool.cond_false, Bool.cond_true, ofVector_toReal, vectorOfPMF_ofVector] at h
  simpa only [w, Bool.cond_false, Bool.cond_true, smul_eq_mul, add_comm] using h

lemma conditionalVector_nonneg (f : α → β) {x : α → ℝ} (hx : x ∈ simplex α) :
    0 ≤ conditionalVector f x := by
  have h := conditionalEntropy_nonneg (ofVector x hx) (Set.toFinite _) f
  simpa only [← conditionalVector_vectorOfPMF, vectorOfPMF_ofVector] using h

lemma conditionalVector_le_card (f : α → β) {x : α → ℝ} (hx : x ∈ simplex α) :
    conditionalVector f x ≤ Fintype.card α := by
  let p := ofVector x hx
  have he : conditionalVector f x = conditionalEntropy p (Set.toFinite _) f := by
    simpa only [p, vectorOfPMF_ofVector] using conditionalVector_vectorOfPMF f p
  rw [he, conditionalEntropy_eq_entropy_sub]
  apply (sub_le_self _ (finiteEntropy_nonneg _ _)).trans
  apply (finiteEntropy_le_log_card _ _).trans
  apply (Real.log_le_self (Nat.cast_nonneg _)).trans
  exact_mod_cast Finset.card_le_univ (Set.toFinite p.support).toFinset

lemma norm_le_one_of_mem_simplex {x : α → ℝ} (hx : x ∈ simplex α) : ‖x‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro a
  rw [Real.norm_eq_abs, abs_of_nonneg (hx.1 a)]
  exact (coordinate_mem_Icc hx a).2

variable {Ω : Type*} [MeasurableSpace Ω]

lemma integrable_probabilityVector (θ : Measure Ω) [IsFiniteMeasure θ]
    (F : Ω → α → ℝ) (hF : Measurable F) (hprob : ∀ᵐ ω ∂θ, F ω ∈ simplex α) :
    Integrable F θ := by
  apply Integrable.of_bound hF.aestronglyMeasurable 1
  exact hprob.mono (fun _ h ↦ norm_le_one_of_mem_simplex h)

lemma integrable_conditionalVector (θ : Measure Ω) [IsFiniteMeasure θ]
    (f : α → β) (F : Ω → α → ℝ) (hF : Measurable F)
    (hprob : ∀ᵐ ω ∂θ, F ω ∈ simplex α) :
    Integrable (fun ω ↦ conditionalVector f (F ω)) θ := by
  apply Integrable.of_bound ((continuous_conditionalVector f).measurable.comp hF).aestronglyMeasurable
    (Fintype.card α)
  filter_upwards [hprob] with ω hω
  rw [Real.norm_eq_abs, Function.comp_apply, abs_of_nonneg (conditionalVector_nonneg f hω)]
  exact conditionalVector_le_card f hω

/-- Conditional entropy is concave under any measurable probability mixture of finite vectors. -/
theorem integral_conditionalVector_le (θ : Measure Ω) [IsProbabilityMeasure θ]
    (f : α → β) (F : Ω → α → ℝ) (hF : Measurable F)
    (hprob : ∀ᵐ ω ∂θ, F ω ∈ simplex α) :
    (∫ ω, conditionalVector f (F ω) ∂θ) ≤ conditionalVector f (∫ ω, F ω ∂θ) := by
  exact (concaveOn_conditionalVector f).le_map_integral
    (continuous_conditionalVector f).continuousOn isClosed_simplex hprob
    (integrable_probabilityVector θ F hF hprob) (integrable_conditionalVector θ f F hF hprob)

end ExactOverlaps.ProbabilityVectors
