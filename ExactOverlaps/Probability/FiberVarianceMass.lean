module

public import ExactOverlaps.Probability.PairwiseVariance
public import ExactOverlaps.Probability.ConditionalMoments
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Unnormalized variance in a finite fiber

The minimum quadratic error of the restricted finite law is exactly the
probability of the fiber times the variance of its normalized conditional
law. Null fibers have mass and error zero. This is the finite algebraic
identification used both for interval variance and for cut observations.
-/

@[expose] public section

open scoped BigOperators ENNReal

namespace ExactOverlaps.FiniteProbability

lemma sum_fiber_weights {α β : Type*} [DecidableEq β] (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (b : β) :
    (∑ a ∈ hp.toFinset, if f a = b then (p a).toReal else 0) = ((p.map f) b).toReal := by
  refine Eq.trans ?_ (Entropy.marginal_toReal_eq_finite_sum p hp f b).symm
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> rfl

/-- The quadratic error of the finite measure restricted to a statistic fiber. -/
noncomputable def fiberVarianceMass {α β : Type*} [DecidableEq β] (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (g : α → ℝ) (b : β) : ℝ :=
  FiniteLaw.minimumQuadraticError hp.toFinset
    (fun a ↦ if f a = b then (p a).toReal else 0) g

lemma fiberVarianceMass_nonneg {α β : Type*} [DecidableEq β] (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (g : α → ℝ) (b : β) :
    0 ≤ fiberVarianceMass p hp f g b := by
  apply FiniteLaw.minimumQuadraticError_nonneg
  intro a _
  split_ifs <;> positivity

/-- The error formula agrees with the mass-weighted conditional variance even on null fibers. -/
theorem fiberVarianceMass_eq_mass_mul {α β : Type*} [DecidableEq β] (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (g : α → ℝ) (b : β) :
    fiberVarianceMass p hp f g b = ((p.map f) b).toReal * fiberVariance p hp f g b := by
  let w : α → ℝ := fun a ↦ if f a = b then (p a).toReal else 0
  have hw : ∀ a ∈ hp.toFinset, 0 ≤ w a := by
    intro a _
    dsimp [w]
    split_ifs <;> positivity
  have hmass : (∑ a ∈ hp.toFinset, w a) = ((p.map f) b).toReal :=
    sum_fiber_weights p hp f b
  have hexp (v : α → ℝ) : (∑ a ∈ hp.toFinset, w a * v a) =
      expectation p hp (fun a ↦ if f a = b then v a else 0) := by
    apply Finset.sum_congr rfl
    intro a _
    dsimp [w]
    split_ifs <;> simp
  change FiniteLaw.minimumQuadraticError hp.toFinset w g = _
  by_cases hm0 : ((p.map f) b).toReal = 0
  · rw [hm0, zero_mul]
    exact FiniteLaw.quadraticError_eq_zero_of_mass_eq_zero hp.toFinset w g hw
      (hmass.trans hm0) _
  · rw [FiniteLaw.minimumQuadraticError_eq_secondMoment_sub hp.toFinset w g hw,
      hmass, hexp (fun a ↦ g a ^ 2), hexp g]
    unfold fiberVariance
    field_simp [hm0]

/-- On positive-mass fibers the normalized law is the actual conditional PMF. -/
theorem fiberVarianceMass_eq_conditional {α β : Type*} [DecidableEq β] (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (g : α → ℝ) (b : (p.map f).support) :
    fiberVarianceMass p hp f g b = ((p.map f) b).toReal *
      variance (Entropy.conditionalPMF p f b)
        (Entropy.conditionalPMF_support_finite p hp f b) g := by
  rw [fiberVarianceMass_eq_mass_mul, fiberVariance_eq_conditional]

/-- The independent-copy square-distance contribution of a fiber is bounded by its variance mass. -/
theorem pairwise_same_fiber_sq_le {α β : Type*} [DecidableEq β] (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (g : α → ℝ) (b : β) :
    (∑ a ∈ hp.toFinset, ∑ a' ∈ hp.toFinset,
      (if f a = b then (p a).toReal else 0) *
        (if f a' = b then (p a').toReal else 0) * (g a - g a') ^ 2) ≤
      2 * fiberVarianceMass p hp f g b := by
  apply FiniteLaw.weighted_pairwise_sq_le_two_minimum
  · intro a _
    split_ifs <;> positivity
  · rw [sum_fiber_weights p hp f b]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using (p.map f).coe_le_one b)

end ExactOverlaps.FiniteProbability
