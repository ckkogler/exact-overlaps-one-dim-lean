/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.PSeries
public import Mathlib.Tactic

/-!
# A summable power envelope for entropy tails

The bound -p log p ≤ 4 p^(3/4) turns quadratic cell-probability decay into
the summable integer power |k|^(-3/2). No finite-support hypothesis enters
this analytic bound.
-/

@[expose] public section

noncomputable section

namespace ExactOverlaps.GaussianScaleEntropy

lemma negMulLog_le_four_rpow {p : ℝ} (hp : 0 ≤ p) :
    Real.negMulLog p ≤ 4 * p ^ (3 / 4 : ℝ) := by
  rcases eq_or_lt_of_le hp with h | hp
  · subst p
    simp
  have h := mul_le_mul_of_nonneg_left
    (Real.log_le_rpow_div (inv_nonneg.mpr hp.le) (by norm_num : (0 : ℝ) < 1 / 4)) hp.le
  have he : p * ((p⁻¹) ^ (1 / 4 : ℝ) / (1 / 4 : ℝ)) =
      4 * p ^ (3 / 4 : ℝ) := by
    rw [Real.inv_rpow hp.le, ← Real.rpow_neg hp.le]
    have hs : p * p ^ (-(1 / 4 : ℝ)) = p ^ (3 / 4 : ℝ) := by
      calc
        _ = p ^ (1 : ℝ) * p ^ (-(1 / 4 : ℝ)) := by rw [Real.rpow_one]
        _ = p ^ ((1 : ℝ) + -(1 / 4 : ℝ)) := (Real.rpow_add hp _ _).symm
        _ = _ := by norm_num
    calc
      _ = 4 * (p * p ^ (-(1 / 4 : ℝ))) := by ring
      _ = _ := by rw [hs]
  rw [he] at h
  simpa only [Real.log_inv, Real.negMulLog_def, mul_neg, neg_mul] using h

lemma summable_entropy_power : Summable (fun k : ℤ ↦ |(k : ℝ)| ^ (-(3 / 2 : ℝ))) :=
  Real.summable_abs_int_rpow (by norm_num)

end ExactOverlaps.GaussianScaleEntropy
