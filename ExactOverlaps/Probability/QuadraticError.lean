module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite weighted quadratic error

The least squared error of a finite nonnegative measure is its mass times
the variance of its normalization. The definitions below include the zero
measure, whose error is zero for every center. They give the algebraic
foundation for local variance on an interval.
-/

@[expose] public section

open scoped BigOperators

namespace ExactOverlaps.FiniteLaw

/-- Squared error about `c` for finite weights, without normalizing their mass. -/
noncomputable def quadraticError {ι : Type*} (s : Finset ι) (w x : ι → ℝ)
    (c : ℝ) : ℝ := ∑ i ∈ s, w i * (x i - c) ^ 2

/-- The normalized first moment, with value zero when the total mass is zero. -/
noncomputable def weightedMean {ι : Type*} (s : Finset ι) (w x : ι → ℝ) : ℝ :=
  (∑ i ∈ s, w i * x i) / ∑ i ∈ s, w i

/-- Minimum quadratic error for nonnegative finite weights. -/
noncomputable def minimumQuadraticError {ι : Type*} (s : Finset ι) (w x : ι → ℝ) : ℝ :=
  quadraticError s w x (weightedMean s w x)

lemma quadraticError_nonneg {ι : Type*} (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (c : ℝ) : 0 ≤ quadraticError s w x c :=
  Finset.sum_nonneg (fun i hi ↦ mul_nonneg (hw i hi) (sq_nonneg _))

lemma quadraticError_expand {ι : Type*} (s : Finset ι) (w x : ι → ℝ) (c : ℝ) :
    quadraticError s w x c =
      (∑ i ∈ s, w i * x i ^ 2) - 2 * c * (∑ i ∈ s, w i * x i) +
        c ^ 2 * (∑ i ∈ s, w i) := by
  unfold quadraticError
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma quadraticError_eq_minimum_add {ι : Type*} (s : Finset ι) (w x : ι → ℝ)
    (hmass : (∑ i ∈ s, w i) ≠ 0) (c : ℝ) :
    quadraticError s w x c = minimumQuadraticError s w x +
      (∑ i ∈ s, w i) * (c - weightedMean s w x) ^ 2 := by
  unfold minimumQuadraticError
  rw [quadraticError_expand, quadraticError_expand]
  unfold weightedMean
  field_simp [hmass]
  ring

lemma quadraticError_eq_zero_of_mass_eq_zero {ι : Type*} (s : Finset ι)
    (w x : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hmass : (∑ i ∈ s, w i) = 0) (c : ℝ) : quadraticError s w x c = 0 := by
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hw).mp hmass
  unfold quadraticError
  apply Finset.sum_eq_zero
  intro i hi
  rw [hz i hi, zero_mul]

lemma minimumQuadraticError_nonneg {ι : Type*} (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) : 0 ≤ minimumQuadraticError s w x :=
  quadraticError_nonneg s w x hw _

/-- The weighted mean minimizes squared error, including the zero-mass case. -/
lemma minimumQuadraticError_le {ι : Type*} (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (c : ℝ) :
    minimumQuadraticError s w x ≤ quadraticError s w x c := by
  by_cases hmass : (∑ i ∈ s, w i) = 0
  · rw [minimumQuadraticError,
      quadraticError_eq_zero_of_mass_eq_zero s w x hw hmass,
      quadraticError_eq_zero_of_mass_eq_zero s w x hw hmass]
  · rw [quadraticError_eq_minimum_add s w x hmass c]
    exact le_add_of_nonneg_right
      (mul_nonneg (Finset.sum_nonneg hw) (sq_nonneg _))

lemma quadraticError_weights_add {ι : Type*} (s : Finset ι)
    (w v x : ι → ℝ) (c : ℝ) :
    quadraticError s (fun i ↦ w i + v i) x c =
      quadraticError s w x c + quadraticError s v x c := by
  simp [quadraticError, add_mul, Finset.sum_add_distrib]

lemma quadraticError_weights_mul {ι : Type*} (s : Finset ι)
    (w x : ι → ℝ) (a c : ℝ) :
    quadraticError s (fun i ↦ a * w i) x c = a * quadraticError s w x c := by
  simp [quadraticError, Finset.mul_sum, mul_assoc]

/-- The minimum of linear quadratic-error functionals is concave in the weights. -/
lemma minimumQuadraticError_concave {ι : Type*} (s : Finset ι)
    (w v x : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) (hv : ∀ i ∈ s, 0 ≤ v i)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * minimumQuadraticError s w x + b * minimumQuadraticError s v x ≤
      minimumQuadraticError s (fun i ↦ a * w i + b * v i) x := by
  unfold minimumQuadraticError
  rw [quadraticError_weights_add, quadraticError_weights_mul,
    quadraticError_weights_mul]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (minimumQuadraticError_le s w x hw _) ha)
    (mul_le_mul_of_nonneg_left (minimumQuadraticError_le s v x hv _) hb)

/-- Midpoint squared error is at most one quarter of mass times interval length squared. -/
lemma quadraticError_midpoint_le {ι : Type*} (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) {a b : ℝ}
    (hx : ∀ i ∈ s, a ≤ x i ∧ x i ≤ b) :
    quadraticError s w x ((a + b) / 2) ≤ (∑ i ∈ s, w i) * (b - a) ^ 2 / 4 := by
  have hpoint (i : ι) (hi : i ∈ s) :
      (x i - (a + b) / 2) ^ 2 ≤ (b - a) ^ 2 / 4 := by
    have h := mul_nonneg (sub_nonneg.mpr (hx i hi).1) (sub_nonneg.mpr (hx i hi).2)
    nlinarith
  calc
    quadraticError s w x ((a + b) / 2) ≤ ∑ i ∈ s, w i * ((b - a) ^ 2 / 4) :=
      Finset.sum_le_sum (fun i hi ↦ mul_le_mul_of_nonneg_left (hpoint i hi) (hw i hi))
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- The local variance bound with the sharp elementary constant one quarter. -/
lemma minimumQuadraticError_le_interval {ι : Type*} (s : Finset ι)
    (w x : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) {a b : ℝ}
    (hx : ∀ i ∈ s, a ≤ x i ∧ x i ≤ b) :
    minimumQuadraticError s w x ≤ (∑ i ∈ s, w i) * (b - a) ^ 2 / 4 :=
  (minimumQuadraticError_le s w x hw ((a + b) / 2)).trans
    (quadraticError_midpoint_le s w x hw hx)

end ExactOverlaps.FiniteLaw
