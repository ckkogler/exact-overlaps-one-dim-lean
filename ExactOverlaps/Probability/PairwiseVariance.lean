module

public import ExactOverlaps.Probability.QuadraticError
public import ExactOverlaps.Probability.FiniteMoments
public import ExactOverlaps.Probability.Dispersion
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Pairwise distance and unnormalized variance

These identities connect the finite quadratic-error minimization with
independent-copy formulas. The weights need not have total mass one, so
they apply directly to an interval-restricted finite probability law.
-/

@[expose] public section

open scoped BigOperators ENNReal

namespace ExactOverlaps.FiniteLaw

lemma weighted_pairwise_sq_expand {ι : Type*} (s : Finset ι) (w x : ι → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, w i * w j * (x i - x j) ^ 2) =
      2 * ((∑ i ∈ s, w i) * (∑ i ∈ s, w i * x i ^ 2) - (∑ i ∈ s, w i * x i) ^ 2) := by
  have he (i j : ι) : w i * w j * (x i - x j) ^ 2 =
      (w i * x i ^ 2) * w j + w i * (w j * x j ^ 2) -
        (2 * (w i * x i)) * (w j * x j) := by ring
  simp_rw [he, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  simp_rw [← Finset.mul_sum]
  ring

/-- The independent-copy identity for a finite measure, including zero mass. -/
lemma weighted_pairwise_sq_eq_minimum {ι : Type*} (s : Finset ι)
    (w x : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, ∑ j ∈ s, w i * w j * (x i - x j) ^ 2) =
      2 * (∑ i ∈ s, w i) * minimumQuadraticError s w x := by
  by_cases hmass : (∑ i ∈ s, w i) = 0
  · have hz := (Finset.sum_eq_zero_iff_of_nonneg hw).mp hmass
    rw [hmass, mul_zero, zero_mul]
    apply Finset.sum_eq_zero
    intro i hi
    simp [hz i hi]
  · rw [weighted_pairwise_sq_expand, minimumQuadraticError, quadraticError_expand]
    unfold weightedMean
    field_simp [hmass]
    ring

/-- The closed second-moment expression for the minimum includes zero-mass fibers. -/
lemma minimumQuadraticError_eq_secondMoment_sub {ι : Type*} (s : Finset ι)
    (w x : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    minimumQuadraticError s w x =
      (∑ i ∈ s, w i * x i ^ 2) - (∑ i ∈ s, w i * x i) ^ 2 / (∑ i ∈ s, w i) := by
  by_cases hmass : (∑ i ∈ s, w i) = 0
  · have hz := (Finset.sum_eq_zero_iff_of_nonneg hw).mp hmass
    have hsecond : (∑ i ∈ s, w i * x i ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hz i hi, zero_mul]
    rw [minimumQuadraticError,
      quadraticError_eq_zero_of_mass_eq_zero s w x hw hmass, hmass, hsecond]
    simp
  · rw [minimumQuadraticError, quadraticError_expand]
    unfold weightedMean
    field_simp [hmass]
    ring

/-- In a subprobability fiber, the independent-copy square distance is at most twice its error. -/
lemma weighted_pairwise_sq_le_two_minimum {ι : Type*} (s : Finset ι)
    (w x : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) (hmass : ∑ i ∈ s, w i ≤ 1) :
    (∑ i ∈ s, ∑ j ∈ s, w i * w j * (x i - x j) ^ 2) ≤
      2 * minimumQuadraticError s w x := by
  rw [weighted_pairwise_sq_eq_minimum s w x hw]
  simpa only [mul_one] using mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmass (by norm_num : (0 : ℝ) ≤ 2))
    (minimumQuadraticError_nonneg s w x hw)

/-- With mass one, the minimum quadratic error is the ordinary probability variance. -/
lemma minimumQuadraticError_pmf_eq_variance {α : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → ℝ) :
    minimumQuadraticError hp.toFinset (fun a ↦ (p a).toReal) f =
      FiniteProbability.variance p hp f := by
  unfold minimumQuadraticError weightedMean
  rw [sum_support_mass]
  simp [quadraticError, FiniteProbability.variance, FiniteProbability.expectation]

/-- The dispersion formula agrees with two nested finite expectations. -/
lemma dispersion_eq_expectation {α : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → ℝ) :
    dispersion p hp f = FiniteProbability.expectation p hp (fun a ↦
      FiniteProbability.expectation p hp (fun b ↦ |f a - f b|)) := rfl

lemma dispersion_le_sqrt_two_variance {α : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → ℝ) :
    dispersion p hp f ≤ Real.sqrt (2 * FiniteProbability.variance p hp f) := by
  rw [dispersion_eq_expectation]
  exact FiniteProbability.pairwise_abs_distance_le_sqrt_two_variance p hp f

end ExactOverlaps.FiniteLaw
