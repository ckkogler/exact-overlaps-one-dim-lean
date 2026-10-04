module

public import ExactOverlaps.Probability.OrderedGapCuts
public import ExactOverlaps.Probability.SameCellVariance
public import ExactOverlaps.Probability.PoissonKernels
import Mathlib.Tactic.Ring

/-!
# Conditional variance under finite Poisson cuts

The variance curve is the finite average of the actual conditional
variances of cut cells. Its independent-copy lower bound has the exact
Poisson exponential kernel, whose time integral is the pairwise dispersion.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal Classical

namespace ExactOverlaps.Poisson

/-- Average conditional variance after observing a finite ordered-gap cut state. -/
noncomputable def cutVariance {n : ℕ} (p : PMF (Fin (n + 1)))
    (hp : p.support.Finite) (x : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ c : Fin n → Bool, cutWeight (orderedGapLength x n) t c *
    FiniteProbability.meanConditionalVariance p hp (cutLabel (indexSide n) c) (fun a ↦ x a.val)

lemma cutVariance_nonneg {n : ℕ} (p : PMF (Fin (n + 1)))
    (hp : p.support.Finite) (x : ℕ → ℝ) (hx : MonotoneOn x (Set.Icc 0 n))
    {t : ℝ} (ht : 0 ≤ t) : 0 ≤ cutVariance p hp x t := by
  apply Finset.sum_nonneg
  intro c _
  exact mul_nonneg (cutWeight_nonneg _ (orderedGapLength_nonneg x n hx) ht c)
    (FiniteProbability.meanConditionalVariance_nonneg p hp _ _)

/-- The retained independent-copy square distance at time `t`. -/
noncomputable def pairSurvival {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (x : α → ℝ) (t : ℝ) : ℝ :=
  ∑ a ∈ hp.toFinset, ∑ b ∈ hp.toFinset,
    (p a).toReal * (p b).toReal * (x a - x b) ^ 2 * Real.exp (-(|x a - x b| * t))

lemma pairSurvival_eq_cut_average {n : ℕ} (p : PMF (Fin (n + 1)))
    (hp : p.support.Finite) (x : ℕ → ℝ) (hx : MonotoneOn x (Set.Icc 0 n))
    (t : ℝ) (ht : 0 ≤ t) :
    pairSurvival p hp (fun a ↦ x a.val) t =
      ∑ c : Fin n → Bool, cutWeight (orderedGapLength x n) t c *
        FiniteProbability.sameCellSquareDistance p hp
          (cutLabel (indexSide n) c) (fun a ↦ x a.val) := by
  unfold pairSurvival FiniteProbability.sameCellSquareDistance
  simp_rw [Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  have hprob := orderedCutPMF_same_label x n hx t ht a b
  simp only [cutPMF_toReal] at hprob
  rw [← hprob, Finset.mul_sum]
  apply Finset.sum_congr (by ext c; simp)
  intro c _
  split_ifs <;> ring

/-- Pointwise independent-copy estimate by twice the actual mean conditional variance. -/
theorem pairSurvival_le_two_cutVariance {n : ℕ} (p : PMF (Fin (n + 1)))
    (hp : p.support.Finite) (x : ℕ → ℝ) (hx : MonotoneOn x (Set.Icc 0 n))
    (t : ℝ) (ht : 0 ≤ t) :
    pairSurvival p hp (fun a ↦ x a.val) t ≤ 2 * cutVariance p hp x t := by
  rw [pairSurvival_eq_cut_average p hp x hx t ht, cutVariance, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c _
  have h := mul_le_mul_of_nonneg_left
    (FiniteProbability.sameCellSquareDistance_le p hp (cutLabel (indexSide n) c)
      (fun a ↦ x a.val)) (cutWeight_nonneg _ (orderedGapLength_nonneg x n hx) ht c)
  simp only [mul_left_comm] at h
  convert h using 1 <;> congr 3

end ExactOverlaps.Poisson
