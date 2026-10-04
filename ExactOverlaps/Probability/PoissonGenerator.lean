module

public import ExactOverlaps.Probability.BooleanCutUpdate
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring

/-!
# The exact finite Poisson reveal generator

A finite cut average is differentiable as a finite sum of products of
exponentials. Pairing the two states of each Boolean coordinate expresses
its derivative as the rate-weighted increment from adding that cut.
-/

@[expose] public section

open scoped BigOperators Classical

namespace ExactOverlaps.Poisson

noncomputable def cutWeightExcept {ι : Type*} [Fintype ι] (d : ι → ℝ)
    (t : ℝ) (c : ι → Bool) (i : ι) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, if c j then 1 - Real.exp (-(d j * t)) else Real.exp (-(d j * t))

lemma cutWeightExcept_update {ι : Type*} [Fintype ι] (d : ι → ℝ)
    (t : ℝ) (c : ι → Bool) (i : ι) (b : Bool) :
    cutWeightExcept d t (Function.update c i b) i = cutWeightExcept d t c i := by
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

lemma cutWeight_eq_factor_mul_except {ι : Type*} [Fintype ι] (d : ι → ℝ)
    (t : ℝ) (c : ι → Bool) (i : ι) :
    cutWeight d t c =
      (if c i then 1 - Real.exp (-(d i * t)) else Real.exp (-(d i * t))) *
        cutWeightExcept d t c i := by
  exact (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)).symm

lemma hasDerivAt_cutFactor (d t : ℝ) (b : Bool) :
    HasDerivAt (fun s ↦ if b then 1 - Real.exp (-(d * s)) else Real.exp (-(d * s)))
      (if b then d * Real.exp (-(d * t)) else -d * Real.exp (-(d * t))) t := by
  have he := (((hasDerivAt_id t).const_mul d).neg).exp
  cases b
  · simpa [mul_comm] using he
  · simpa [mul_comm] using he.const_sub 1

lemma hasDerivAt_cutWeight {ι : Type*} [Fintype ι] (d : ι → ℝ)
    (t : ℝ) (c : ι → Bool) :
    HasDerivAt (fun s ↦ cutWeight d s c)
      (∑ i, cutWeightExcept d t c i *
        (if c i then d i * Real.exp (-(d i * t)) else -d i * Real.exp (-(d i * t)))) t := by
  simpa only [cutWeight, cutWeightExcept, smul_eq_mul] using
    HasDerivAt.fun_finsetProd (u := Finset.univ)
      (fun i _ ↦ hasDerivAt_cutFactor (d i) t (c i))

noncomputable def cutAverage {ι : Type*} [Fintype ι] (d : ι → ℝ)
    (f : (ι → Bool) → ℝ) (t : ℝ) : ℝ := ∑ c, cutWeight d t c * f c

lemma cutAverage_derivative_algebra {ι : Type*} [Fintype ι] (d : ι → ℝ)
    (f : (ι → Bool) → ℝ) (t : ℝ) :
    (∑ c : ι → Bool, (∑ i, cutWeightExcept d t c i *
      (if c i then d i * Real.exp (-(d i * t)) else -d i * Real.exp (-(d i * t)))) * f c) =
    ∑ c : ι → Bool, cutWeight d t c *
      ∑ i, if c i then 0 else d i * (f (Function.update c i true) - f c) := by
  let w (i : ι) (c : ι → Bool) := d i * Real.exp (-(d i * t)) * cutWeightExcept d t c i
  have hw (i : ι) (c : ι → Bool) (b : Bool) : w i (Function.update c i b) = w i c := by
    simp only [w, cutWeightExcept_update]
  calc
    _ = ∑ c : ι → Bool, ∑ i, w i c * (if c i then f c else -f c) := by
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      cases c i <;> simp only [Bool.false_eq_true, ite_false, ite_true, w] <;> ring
    _ = ∑ i, ∑ c : ι → Bool, w i c * (if c i then f c else -f c) := Finset.sum_comm
    _ = ∑ i, ∑ c : ι → Bool,
        if c i then 0 else w i c * (f (Function.update c i true) - f c) := by
      apply Finset.sum_congr rfl
      intro i _
      exact sum_signed_cut_eq_increments i (w i) f (hw i)
    _ = ∑ c : ι → Bool, ∑ i,
        if c i then 0 else w i c * (f (Function.update c i true) - f c) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      cases hc : c i
      · rw [cutWeight_eq_factor_mul_except d t c i]
        simp only [hc, Bool.false_eq_true, ite_false, w]
        ring
      · simp

theorem hasDerivAt_cutAverage {ι : Type*} [Fintype ι] (d : ι → ℝ)
    (f : (ι → Bool) → ℝ) (t : ℝ) :
    HasDerivAt (cutAverage d f)
      (∑ c : ι → Bool, cutWeight d t c *
        ∑ i, if c i then 0 else d i * (f (Function.update c i true) - f c)) t := by
  rw [← cutAverage_derivative_algebra d f t]
  exact HasDerivAt.fun_sum (fun c _ ↦ (hasDerivAt_cutWeight d t c).mul_const (f c))

end ExactOverlaps.Poisson
