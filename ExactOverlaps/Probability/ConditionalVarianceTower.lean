module

public import ExactOverlaps.Probability.ConditionalRefinement
import Mathlib.Tactic.FieldSimp

/-!
# Conditional variance under a second finite observation

The normalized second-observation variance is the original joint-fiber
variance, including null second fibers. This is the moment interface behind
averaging variance over successive cut refinements.
-/

@[expose] public section

open scoped BigOperators ENNReal Classical

namespace ExactOverlaps.FiniteProbability

lemma expectation_joint_indicator {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (p : PMF α) (hp : p.support.Finite) (f : α → β) (g : α → γ)
    (b : β) (c : γ) (v : α → ℝ) :
    expectation p hp (fun a ↦ if f a = b then (if g a = c then v a else 0) else 0) =
      expectation p hp (fun a ↦ if (f a, g a) = (b, c) then v a else 0) := by
  unfold expectation
  apply Finset.sum_congr rfl
  intro a _
  by_cases hf : f a = b <;> by_cases hg : g a = c <;> simp [hf, hg]

/-- Refining a positive first fiber gives the variance of the original joint fiber. -/
lemma fiberVariance_conditional {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (p : PMF α) (hp : p.support.Finite) (f : α → β) (g : α → γ)
    (x : α → ℝ) (b : (p.map f).support) (c : γ) :
    fiberVariance (Entropy.conditionalPMF p f b)
      (Entropy.conditionalPMF_support_finite p hp f b) g x c =
      fiberVariance p hp (fun a ↦ (f a, g a)) x (b.val, c) := by
  unfold fiberVariance
  rw [expectation_conditional p hp, expectation_conditional p hp,
    expectation_joint_indicator p hp, expectation_joint_indicator p hp,
    Entropy.conditionalPMF_map_apply, ENNReal.toReal_div]
  simp only [div_div_div_cancel_right₀ (Entropy.marginal_toReal_pos p f b).ne']

/-- Averaging the actual conditional expectations reconstructs the original expectation. -/
lemma sum_marginal_mul_expectation_conditional {α β : Type*} [DecidableEq β]
    (p : PMF α) (hp : p.support.Finite) (f : α → β) (v : α → ℝ) :
    (letI : Fintype (p.map f).support :=
      (show (p.map f).support.Finite from by simpa using hp.image f).fintype
    ∑ b : (p.map f).support, ((p.map f) b).toReal *
      expectation (Entropy.conditionalPMF p f b)
        (Entropy.conditionalPMF_support_finite p hp f b) v) = expectation p hp v := by
  let : Fintype (p.map f).support :=
    (show (p.map f).support.Finite from by simpa using hp.image f).fintype
  change (∑ b : (p.map f).support, _) = _
  simp_rw [expectation_conditional p hp]
  simp_rw [mul_div_cancel₀ _ (Entropy.marginal_toReal_pos p f _).ne']
  unfold expectation
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.mul_sum]
  have hfa : f a ∈ (p.map f).support :=
    (PMF.mem_support_map_iff f p (f a)).mpr ⟨a, by simpa using ha, rfl⟩
  rw [Finset.sum_eq_single (⟨f a, hfa⟩ : (p.map f).support)]
  · simp
  · intro b _ hb
    have hne : f a ≠ b.val := fun he ↦ hb (Subtype.ext he.symm)
    simp [hne]
  · simp

/-- Mean variance under a refined observation is the average of the conditional refinements. -/
lemma meanConditionalVariance_tower {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (p : PMF α) (hp : p.support.Finite) (f : α → β) (g : α → γ) (x : α → ℝ) :
    (letI : Fintype (p.map f).support :=
      (show (p.map f).support.Finite from by simpa using hp.image f).fintype
    ∑ b : (p.map f).support, ((p.map f) b).toReal *
      meanConditionalVariance (Entropy.conditionalPMF p f b)
        (Entropy.conditionalPMF_support_finite p hp f b) g x) =
      meanConditionalVariance p hp (fun a ↦ (f a, g a)) x := by
  let : Fintype (p.map f).support :=
    (show (p.map f).support.Finite from by simpa using hp.image f).fintype
  let v : α → ℝ := fun a ↦ fiberVariance p hp (fun z ↦ (f z, g z)) x (f a, g a)
  change (∑ b : (p.map f).support, _) = expectation p hp v
  rw [← sum_marginal_mul_expectation_conditional p hp f v]
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  unfold meanConditionalVariance expectation
  apply Finset.sum_congr rfl
  intro a ha
  have hmem : a ∈ (Entropy.conditionalPMF p f b).support := by simpa using ha
  rw [Entropy.conditionalPMF_support] at hmem
  have hfa : f a = b := hmem.1
  dsimp only
  rw [fiberVariance_conditional p hp f g x b]
  simp only [v, hfa]

/-- Conditional variance depends on the partition fibers, not on their names. -/
lemma meanConditionalVariance_congr_fibers {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (p : PMF α) (hp : p.support.Finite) (f : α → β) (g : α → γ) (x : α → ℝ)
    (hfg : ∀ a b, f a = f b ↔ g a = g b) :
    meanConditionalVariance p hp f x = meanConditionalVariance p hp g x := by
  unfold meanConditionalVariance expectation
  apply Finset.sum_congr rfl
  intro a ha
  have hfa : f a ∈ (p.map f).support :=
    (PMF.mem_support_map_iff f p (f a)).mpr ⟨a, by simpa using ha, rfl⟩
  have hga : g a ∈ (p.map g).support :=
    (PMF.mem_support_map_iff g p (g a)).mpr ⟨a, by simpa using ha, rfl⟩
  dsimp only
  rw [fiberVariance_eq_conditional p hp f x ⟨f a, hfa⟩,
    fiberVariance_eq_conditional p hp g x ⟨g a, hga⟩]
  have he := Entropy.conditionalPMF_eq_of_fiber_eq p f g ⟨f a, hfa⟩ ⟨g a, hga⟩
    (fun b ↦ hfg b a)
  have hvar {q q' : PMF α} (hq : q.support.Finite) (hq' : q'.support.Finite)
      (heq : q = q') : variance q hq x = variance q' hq' x := by
    subst q'
    rfl
  rw [hvar _ _ he]

end ExactOverlaps.FiniteProbability
