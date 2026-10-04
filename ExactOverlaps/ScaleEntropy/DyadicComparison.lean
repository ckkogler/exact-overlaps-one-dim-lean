/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.ScaleEntropy.Averaged
public import ExactOverlaps.SelfSimilar.ShiftedDyadicEntropy

/-!
# Comparing averaged entropy with dyadic entropy

At a dyadic mesh, physical translation is a rescaled dimensionless grid
translation. The sharp `log 2` comparison survives averaging, with atoms on
grid boundaries allowed. All entropies use natural logarithms.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace ExactOverlaps.ScaleEntropy

open Entropy

lemma quantize_dyadic (i : ℤ) (t x : ℝ) :
    quantize ((2 : ℝ) ^ (-i)) t x = shiftedDyadicQuantize i ((2 : ℝ) ^ i * t) x := by
  unfold quantize shiftedDyadicQuantize
  congr 1
  simp only [div_eq_mul_inv, zpow_neg, inv_inv, add_mul, mul_comm]

lemma law_dyadic (μ : ProbabilityMeasure ℝ) (i : ℤ) (t : ℝ) :
    law μ ((2 : ℝ) ^ (-i)) t = shiftedDyadicLaw μ i ((2 : ℝ) ^ i * t) := by
  unfold law shiftedDyadicLaw
  congr 3
  funext x
  exact quantize_dyadic i t x

lemma shiftedEntropy_dyadic (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ)
    (i : ℤ) (t : ℝ) :
    shiftedEntropy μ hμ ((2 : ℝ) ^ (-i)) (dyadic_scale_pos (-i)) t =
      shiftedDyadicEntropy μ hμ i ((2 : ℝ) ^ i * t) := by
  exact finiteEntropy_congr (law_dyadic μ i t) _ _

lemma abs_shiftedEntropy_dyadic_sub_le_log_two (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) (t : ℝ) :
    |shiftedEntropy μ hμ ((2 : ℝ) ^ (-i)) (dyadic_scale_pos (-i)) t -
      dyadicEntropy μ hμ i| ≤ Real.log 2 := by
  rw [shiftedEntropy_dyadic]
  exact abs_shiftedDyadicEntropy_sub_le_log_two μ hμ i _

/-- Averaging the translated dyadic grids changes entropy by at most `log 2`. -/
theorem abs_entropy_dyadic_sub_le_log_two (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) :
    |entropy μ hμ ((2 : ℝ) ^ (-i)) (dyadic_scale_pos (-i)) -
      dyadicEntropy μ hμ i| ≤ Real.log 2 := by
  let r : ℝ := (2 : ℝ) ^ (-i)
  have hr : 0 < r := dyadic_scale_pos (-i)
  have hi := intervalIntegrable_shiftedEntropy μ hμ r hr 0 r
  have hb (t : ℝ) := abs_le.mp (abs_shiftedEntropy_dyadic_sub_le_log_two μ hμ i t)
  have hl := intervalIntegral.integral_mono_on hr.le intervalIntegrable_const hi
    (fun t _ ↦ (show dyadicEntropy μ hμ i - Real.log 2 ≤ shiftedEntropy μ hμ r hr t by
      linarith [(hb t).1]))
  have hu := intervalIntegral.integral_mono_on hr.le hi intervalIntegrable_const
    (fun t _ ↦ (show shiftedEntropy μ hμ r hr t ≤ dyadicEntropy μ hμ i + Real.log 2 by
      linarith [(hb t).2]))
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hl hu
  have hlo : dyadicEntropy μ hμ i - Real.log 2 ≤ entropy μ hμ r hr := by
    apply (le_div_iff₀ hr).mpr
    nlinarith [hl]
  have hup : entropy μ hμ r hr ≤ dyadicEntropy μ hμ i + Real.log 2 := by
    apply (div_le_iff₀ hr).mpr
    nlinarith [hu]
  apply abs_le.mpr
  constructor <;> linarith

end ExactOverlaps.ScaleEntropy
