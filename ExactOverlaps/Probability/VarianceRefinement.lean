module

public import ExactOverlaps.Probability.ConditionalVarianceTower
public import ExactOverlaps.Probability.CutRefinementAverage
public import ExactOverlaps.Probability.PoissonVariance

/-!
# Averaging conditional variance under Poisson refinement

Condition inside a cut cell, add an independent cut state, and average over
the cell and both states. The resulting mean variance is exactly the curve
at the sum of the two intensities.
-/

@[expose] public section

open scoped BigOperators ENNReal Classical

namespace ExactOverlaps.Poisson

lemma meanConditionalVariance_unionCuts {ι α : Type*} [Fintype ι]
    (p : PMF α) (hp : p.support.Finite) (side : ι → α → Bool)
    (c c' : ι → Bool) (x : α → ℝ) :
    FiniteProbability.meanConditionalVariance p hp (cutLabel side (unionCuts c c')) x =
      FiniteProbability.meanConditionalVariance p hp
        (fun a ↦ (cutLabel side c a, cutLabel side c' a)) x := by
  apply FiniteProbability.meanConditionalVariance_congr_fibers
  intro a b
  simp only [Prod.mk.injEq]
  exact cutLabel_union_eq_iff side c c' a b

lemma average_conditional_refinement_variance {ι α : Type*} [Fintype ι]
    (p : PMF α) (hp : p.support.Finite) (side : ι → α → Bool)
    (c c' : ι → Bool) (x : α → ℝ) :
    (letI : Fintype (p.map (cutLabel side c)).support :=
      (show (p.map (cutLabel side c)).support.Finite from
        by simpa using hp.image (cutLabel side c)).fintype
    ∑ b : (p.map (cutLabel side c)).support, ((p.map (cutLabel side c)) b).toReal *
      FiniteProbability.meanConditionalVariance
        (Entropy.conditionalPMF p (cutLabel side c) b)
        (Entropy.conditionalPMF_support_finite p hp (cutLabel side c) b)
        (cutLabel side c') x) =
      FiniteProbability.meanConditionalVariance p hp (cutLabel side (unionCuts c c')) x := by
  rw [FiniteProbability.meanConditionalVariance_tower,
    meanConditionalVariance_unionCuts]

/-- Average of the future variance curve over the observed cells of a fixed cut state. -/
noncomputable def conditionalCutVariance {n : ℕ} (p : PMF (Fin (n + 1)))
    (hp : p.support.Finite) (x : ℕ → ℝ) (c : Fin n → Bool) (u : ℝ) : ℝ :=
  letI : Fintype (p.map (cutLabel (indexSide n) c)).support :=
    (show (p.map (cutLabel (indexSide n) c)).support.Finite from
      by simpa using hp.image (cutLabel (indexSide n) c)).fintype
  ∑ b : (p.map (cutLabel (indexSide n) c)).support,
    ((p.map (cutLabel (indexSide n) c)) b).toReal *
      cutVariance (Entropy.conditionalPMF p (cutLabel (indexSide n) c) b)
        (Entropy.conditionalPMF_support_finite p hp (cutLabel (indexSide n) c) b) x u

lemma conditionalCutVariance_eq {n : ℕ} (p : PMF (Fin (n + 1)))
    (hp : p.support.Finite) (x : ℕ → ℝ) (c : Fin n → Bool) (u : ℝ) :
    conditionalCutVariance p hp x c u =
      ∑ c' : Fin n → Bool, cutWeight (orderedGapLength x n) u c' *
        FiniteProbability.meanConditionalVariance p hp
          (cutLabel (indexSide n) (unionCuts c c')) (fun a ↦ x a.val) := by
  let : Fintype (p.map (cutLabel (indexSide n) c)).support :=
    (show (p.map (cutLabel (indexSide n) c)).support.Finite from
      by simpa using hp.image (cutLabel (indexSide n) c)).fintype
  unfold conditionalCutVariance cutVariance
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr (by ext c'; simp)
  intro c' _
  rw [← average_conditional_refinement_variance p hp (indexSide n) c c' (fun a ↦ x a.val),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The conditional variance semigroup identity for the genuine cut observations. -/
theorem average_conditionalCutVariance {n : ℕ} (p : PMF (Fin (n + 1)))
    (hp : p.support.Finite) (x : ℕ → ℝ) (t u : ℝ) :
    (∑ c : Fin n → Bool, cutWeight (orderedGapLength x n) t c *
      conditionalCutVariance p hp x c u) = cutVariance p hp x (t + u) := by
  simp_rw [conditionalCutVariance_eq]
  unfold cutVariance
  have h := sum_cutWeight_union_apply (orderedGapLength x n) t u
    (fun c ↦ FiniteProbability.meanConditionalVariance p hp
      (cutLabel (indexSide n) c) (fun a ↦ x a.val))
  convert h using 1
  · apply Finset.sum_congr (by ext c; simp)
    intro c _
    congr 1
    apply Finset.sum_congr (by ext c'; simp)
    intro c' _
    rfl
  · apply Finset.sum_congr (by ext c; simp)
    intro c _
    rfl

end ExactOverlaps.Poisson
