module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Scalar kernels for finite Poisson partitions

An interval containing a pair of atoms at distance `d` has offset length
`(r-d)₊`; the probability that Poisson cuts of intensity `t` leave the pair
unseparated is `exp(-d*t)`. The exact integrals below connect the two
descriptions of variance energy. Positive atom separation is explicit.
-/

@[expose] public section

open MeasureTheory Set

namespace ExactOverlaps.Poisson

/-- The polynomial moments of the exponential survival kernel. -/
lemma integral_pow_mul_exp {d : ℝ} (hd : 0 < d) (k : ℕ) :
    (∫ t : ℝ in Ioi 0, t ^ k * Real.exp (-(d * t))) =
      (Nat.factorial k : ℝ) / d ^ (k + 1) := by
  have key := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (k : ℝ) + 1) (r := d) (by positivity) hd
  have he : ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) := by norm_num
  have hp : (1 / d) ^ ((k : ℝ) + 1) = 1 / d ^ (k + 1) := by
    rw [he, Real.rpow_natCast]
    simp
  simp only [add_sub_cancel_right, Real.rpow_natCast,
    Real.Gamma_nat_eq_factorial, hp] at key
  simpa [div_eq_mul_inv, mul_comm] using key

lemma integrableOn_pow_mul_exp {d : ℝ} (hd : 0 < d) (k : ℕ) :
    IntegrableOn (fun t : ℝ ↦ t ^ k * Real.exp (-(d * t))) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_pow_mul_exp hd k]
  positivity

lemma integral_time_mul_exp {d : ℝ} (hd : 0 < d) :
    (∫ t : ℝ in Ioi 0, t * Real.exp (-(d * t))) = 1 / d ^ 2 := by
  simpa using integral_pow_mul_exp hd 1

lemma integral_cube_mul_exp {d : ℝ} (hd : 0 < d) :
    (∫ t : ℝ in Ioi 0, t ^ 3 * Real.exp (-(d * t))) = 6 / d ^ 4 := by
  simpa [Nat.factorial] using integral_pow_mul_exp hd 3

lemma integrableOn_inv_cube {d : ℝ} (hd : 0 < d) :
    IntegrableOn (fun r : ℝ ↦ 1 / r ^ 3) (Ioi d) := by
  simpa only [Real.rpow_neg_ofNat, zpow_neg, zpow_ofNat, one_div] using
    integrableOn_Ioi_rpow_of_lt (a := (-3 : ℝ)) (by norm_num) hd

lemma integrableOn_inv_fourth {d : ℝ} (hd : 0 < d) :
    IntegrableOn (fun r : ℝ ↦ 1 / r ^ 4) (Ioi d) := by
  simpa only [Real.rpow_neg_ofNat, zpow_neg, zpow_ofNat, one_div] using
    integrableOn_Ioi_rpow_of_lt (a := (-4 : ℝ)) (by norm_num) hd

lemma integral_inv_cube {d : ℝ} (hd : 0 < d) :
    (∫ r : ℝ in Ioi d, 1 / r ^ 3) = 1 / (2 * d ^ 2) := by
  have h := integral_Ioi_rpow_of_lt (a := (-3 : ℝ)) (by norm_num) hd
  norm_num [Real.rpow_neg_ofNat, zpow_neg, zpow_natCast] at h
  simpa [one_div, div_eq_mul_inv, mul_comm] using h

lemma integral_inv_fourth {d : ℝ} (hd : 0 < d) :
    (∫ r : ℝ in Ioi d, 1 / r ^ 4) = 1 / (3 * d ^ 3) := by
  have h := integral_Ioi_rpow_of_lt (a := (-4 : ℝ)) (by norm_num) hd
  norm_num [Real.rpow_neg_ofNat, zpow_neg, zpow_natCast] at h
  simpa [one_div, div_eq_mul_inv, mul_comm] using h

/-- The offset-length integral above the atom separation has the exact factor `1/6`. -/
lemma integral_offset_length {d : ℝ} (hd : 0 < d) :
    (∫ r : ℝ in Ioi d, (r - d) / r ^ 4) = 1 / (6 * d ^ 2) := by
  have hfun : Set.EqOn (fun r : ℝ ↦ (r - d) / r ^ 4)
      (fun r : ℝ ↦ 1 / r ^ 3 - d * (1 / r ^ 4)) (Ioi d) := by
    intro r hr
    have hr0 : r ≠ 0 := (hd.trans hr).ne'
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hfun,
    integral_sub (integrableOn_inv_cube hd) ((integrableOn_inv_fourth hd).const_mul d),
    integral_const_mul, integral_inv_cube hd, integral_inv_fourth hd]
  field_simp
  ring

/-- The same offset kernel on all positive scales, including scales below separation. -/
lemma integral_positive_offset_length {d : ℝ} (hd : 0 < d) :
    (∫ r : ℝ in Ioi 0, max (r - d) 0 / r ^ 4) = 1 / (6 * d ^ 2) := by
  calc
    (∫ r : ℝ in Ioi 0, max (r - d) 0 / r ^ 4) =
        ∫ r : ℝ in Ioi d, max (r - d) 0 / r ^ 4 := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
        (fun r hr ↦ hd.trans hr)
      intro r hr
      have hrd : r ≤ d := le_of_not_gt hr.2
      rw [max_eq_right (sub_nonpos.mpr hrd), zero_div]
    _ = ∫ r : ℝ in Ioi d, (r - d) / r ^ 4 := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      simp only [max_eq_left (sub_nonneg.mpr hr.le)]
    _ = 1 / (6 * d ^ 2) := integral_offset_length hd

lemma integrableOn_positive_offset_length {d : ℝ} (hd : 0 < d) :
    IntegrableOn (fun r : ℝ ↦ max (r - d) 0 / r ^ 4) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_positive_offset_length hd]
  positivity

end ExactOverlaps.Poisson
