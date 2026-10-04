/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
Adapted from the LpSelfSimilar probability library.
-/
module

public import ExactOverlaps.Probability.FiniteMoments
public import ExactOverlaps.Entropy.Conditioning

@[expose] public section

/-!
Finite conditional moments, with a formula on all values of the conditioning
statistic. On every positive-mass fiber this formula is the variance of the
normalized conditional probability law. The formula assigns zero to null fibers.
-/

open MeasureTheory Set
open scoped ENNReal

namespace ExactOverlaps.FiniteProbability

lemma expectation_conditional {α β : Type*} [DecidableEq β] (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (b : (p.map f).support) (g : α → ℝ) :
    expectation (Entropy.conditionalPMF p f b)
      (Entropy.conditionalPMF_support_finite p hp f b) g =
    expectation p hp (fun a ↦ if f a = b then g a else 0) / ((p.map f) b).toReal := by
  classical
  let hq := Entropy.conditionalPMF_support_finite p hp f b
  have hsub : hq.toFinset ⊆ hp.toFinset := by
    intro a ha
    have hmem : a ∈ (Entropy.conditionalPMF p f b).support := by simpa using ha
    rw [Entropy.conditionalPMF_support] at hmem
    simpa using hmem.2
  have he : expectation (Entropy.conditionalPMF p f b) hq g =
      ∑ a ∈ hp.toFinset, (Entropy.conditionalPMF p f b a).toReal * g a := by
    apply Finset.sum_subset hsub
    intro a _ ha
    have hz : Entropy.conditionalPMF p f b a = 0 := by simpa using ha
    simp [hz]
  rw [he, expectation, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  rw [Entropy.conditionalPMF_toReal]
  split_ifs <;> simp_all [div_mul_eq_mul_div]

/-- Variance in a fiber, expressed through its first two unnormalized moments. -/
noncomputable def fiberVariance {α β : Type*} [DecidableEq β] (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (g : α → ℝ) (b : β) : ℝ :=
  expectation p hp (fun a ↦ if f a = b then g a ^ 2 else 0) / ((p.map f) b).toReal -
    (expectation p hp (fun a ↦ if f a = b then g a else 0) / ((p.map f) b).toReal) ^ 2

lemma fiberVariance_eq_conditional {α β : Type*} [DecidableEq β] (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (g : α → ℝ) (b : (p.map f).support) :
    fiberVariance p hp f g b = variance (Entropy.conditionalPMF p f b)
      (Entropy.conditionalPMF_support_finite p hp f b) g := by
  rw [variance_eq_secondMoment_sub, expectation_conditional, expectation_conditional]
  rfl

lemma fiberVariance_nonneg {α β : Type*} [DecidableEq β] (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (g : α → ℝ) (b : β) :
    0 ≤ fiberVariance p hp f g b := by
  by_cases hb : b ∈ (p.map f).support
  · rw [fiberVariance_eq_conditional p hp f g ⟨b, hb⟩]
    exact variance_nonneg _ _ _
  · have hz : (p.map f) b = 0  := by
      change ¬ (p.map f) b ≠ 0 at hb
      exact not_not.mp hb
    simp [fiberVariance, hz]

/-- Mean conditional variance, written over the original atoms. -/
noncomputable def meanConditionalVariance {α β : Type*} [DecidableEq β] (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (g : α → ℝ) : ℝ :=
  expectation p hp (fun a ↦ fiberVariance p hp f g (f a))

lemma meanConditionalVariance_nonneg {α β : Type*} [DecidableEq β] (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (g : α → ℝ) :
    0 ≤ meanConditionalVariance p hp f g :=
  expectation_nonneg p hp (fun a _ ↦ fiberVariance_nonneg p hp f g (f a))

/-- The finite formula is exactly the marginal-weighted sum of conditional variances. -/
lemma meanConditionalVariance_eq {α β : Type*} [DecidableEq β] (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (g : α → ℝ) :
    meanConditionalVariance p hp f g =
    (letI : Fintype (p.map f).support :=
      (show (p.map f).support.Finite from by simpa using hp.image f).fintype
    ∑ b : (p.map f).support, ((p.map f) b).toReal *
      variance (Entropy.conditionalPMF p f b)
        (Entropy.conditionalPMF_support_finite p hp f b) g) := by
  classical
  let hpf : (p.map f).support.Finite := by simpa using hp.image f
  let : Fintype (p.map f).support := hpf.fintype
  change expectation p hp _ = _
  unfold expectation
  rw [← Entropy.sum_marginal_mul p hp f (fiberVariance p hp f g)]
  rw [Finset.sum_subtype hpf.toFinset (by simp : ∀ b, b ∈ hpf.toFinset ↔ b ∈ (p.map f).support)]
  apply Finset.sum_congr rfl
  intro b _
  rw [fiberVariance_eq_conditional]

lemma variance_le_sq_of_diameter {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (g : α → ℝ) {s : ℝ} (hs : 0 ≤ s)
    (hdiam : ∀ a ∈ p.support, ∀ b ∈ p.support, |g a - g b| ≤ s) :
    variance p hp g ≤ s ^ 2 := by
  have he : expectation p hp (fun a ↦ expectation p hp (fun b ↦ (g a - g b) ^ 2)) ≤ s ^ 2 := by
    rw [← expectation_const p hp (s ^ 2)]
    apply expectation_mono p hp
    intro a ha
    rw [← expectation_const p hp (s ^ 2)]
    apply expectation_mono p hp
    intro b hb
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hs).mpr (hdiam a ha b hb)
  rw [pairwise_sq_distance_eq_two_variance] at he
  nlinarith [variance_nonneg p hp g, sq_nonneg s]

end ExactOverlaps.FiniteProbability
