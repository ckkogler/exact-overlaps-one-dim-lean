/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.WImprovement.FiniteLawProfiles
public import ExactOverlaps.ConvolutionDisintegration.VarianceBound
public import ExactOverlaps.StoppedConcatenation.DiscreteWJensen
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Exact variance-to-cost decay

The sliding-window W bound averages with the genuine finite-law weights.
Products of these bounds give exponential decay with exactly the constant
1-exp(-1), before applying the positive concatenation exponent.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace ExactOverlaps.WImprovement

open ConvolutionDisintegration

lemma varianceDecay_pos : 0 < 1 - Real.exp (-1) := by
  have h : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  linarith

lemma meanW_le_one_sub_profile {ι : Type*} [Fintype ι]
    (q : PMF ι) (p : ι → PMF ℝ) {r : ℝ} (hr : 0 < r) :
    (∑ i, (q i).toReal * W (pmfLaw (p i)) r) ≤
      1 - (1 - Real.exp (-1)) * meanVarianceProfile q p r := by
  calc
    _ ≤ ∑ i, (q i).toReal * (1 - (1 - Real.exp (-1)) * varianceProfile (p i).toMeasure r) :=
      Finset.sum_le_sum (fun i _ ↦ mul_le_mul_of_nonneg_left
        (W_le_one_sub_normalizedLocalVariance (pmfLaw (p i)) hr) ENNReal.toReal_nonneg)
    _ = _ := by
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib, Entropy.sum_pmf_toReal,
        meanVarianceProfile, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring

lemma product_decay_of_profile_sum {ι : Type*} [Fintype ι]
    (v w : ι → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hvw : ∀ i, v i ≤ 1 - (1 - Real.exp (-1)) * w i)
    {a η : ℝ} (ha : 0 ≤ a) (hsum : η ≤ ∑ i, w i) :
    (∏ i, v i) ^ a ≤ Real.exp (-a * (1 - Real.exp (-1)) * η) := by
  have hb (i : ι) : v i ≤ Real.exp (-(1 - Real.exp (-1)) * w i) := by
    apply (hvw i).trans
    have h := Real.add_one_le_exp (-(1 - Real.exp (-1)) * w i)
    linarith
  have hp : (∏ i, v i) ≤ Real.exp (-(1 - Real.exp (-1)) * ∑ i, w i) := by
    calc
      _ ≤ ∏ i, Real.exp (-(1 - Real.exp (-1)) * w i) :=
        Finset.prod_le_prod₀ (fun i _ ↦ hv i) (fun i _ ↦ hb i)
      _ = _ := by rw [← Real.exp_sum, ← Finset.mul_sum]
  have hpow := Real.rpow_le_rpow (Finset.prod_nonneg (fun i _ ↦ hv i)) hp ha
  rw [← Real.exp_mul] at hpow
  apply hpow.trans
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_left hsum
    (mul_nonneg ha varianceDecay_pos.le)
  nlinarith

end ExactOverlaps.WImprovement
