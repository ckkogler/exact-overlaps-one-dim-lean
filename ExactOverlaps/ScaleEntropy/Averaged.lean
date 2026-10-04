/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.ScaleEntropy.Measurable
public import ExactOverlaps.Entropy.ConditionalMixture
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Translation-averaged entropy and entropy between scales

At mesh `r`, average the actual shifted partition entropy over one period.
When the coarse mesh is an integer multiple of the fine mesh, their entropy
difference is the average of an actual conditional Shannon entropy over a
common period. This identity is the basis of concavity between scales.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace ExactOverlaps.ScaleEntropy

open Entropy

/-- Entropy at a positive scale, with natural logarithms. -/
def entropy (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ)
    (r : ℝ) (hr : 0 < r) : ℝ :=
  (∫ t in (0 : ℝ)..r, shiftedEntropy μ hμ r hr t) / r

/-- Entropy between two positive scales. -/
def entropyBetween (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ)
    (r : ℝ) (hr : 0 < r) (R : ℝ) (hR : 0 < R) : ℝ :=
  entropy μ hμ r hr - entropy μ hμ R hR

lemma entropy_eq_setIntegral (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ)
    (r : ℝ) (hr : 0 < r) :
    entropy μ hμ r hr = (∫ t in Ioc 0 r, shiftedEntropy μ hμ r hr t) / r := by
  rw [entropy, intervalIntegral.integral_of_le hr.le]

lemma entropy_nonneg (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ)
    (r : ℝ) (hr : 0 < r) : 0 ≤ entropy μ hμ r hr := by
  exact div_nonneg (intervalIntegral.integral_nonneg_of_forall hr.le
    (shiftedEntropy_nonneg μ hμ r hr)) hr.le

lemma entropy_eq_average_from (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ)
    (r : ℝ) (hr : 0 < r) (s : ℝ) :
    entropy μ hμ r hr = (∫ t in s..s + r, shiftedEntropy μ hμ r hr t) / r := by
  have h := (shiftedEntropy_periodic μ hμ r hr).intervalIntegral_add_eq 0 s
  simpa only [entropy, zero_add] using congrArg (fun z : ℝ ↦ z / r) h

lemma integral_shiftedEntropy_nat_mul (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (r : ℝ) (hr : 0 < r) (C : ℕ) :
    (∫ t in (0 : ℝ)..(C : ℝ) * r, shiftedEntropy μ hμ r hr t) =
      (C : ℝ) * ∫ t in (0 : ℝ)..r, shiftedEntropy μ hμ r hr t := by
  have h := (shiftedEntropy_periodic μ hμ r hr).intervalIntegral_add_zsmul_eq
    (C : ℤ) 0 (intervalIntegrable_shiftedEntropy μ hμ r hr)
  simpa only [zero_add, zsmul_eq_mul, Int.cast_natCast] using h

lemma entropy_eq_average_nat_mul (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (r : ℝ) (hr : 0 < r) (C : ℕ) (hC : 0 < C) :
    entropy μ hμ r hr =
      (∫ t in (0 : ℝ)..(C : ℝ) * r, shiftedEntropy μ hμ r hr t) / ((C : ℝ) * r) := by
  rw [entropy, integral_shiftedEntropy_nat_mul]
  have hC' : (C : ℝ) ≠ 0 := by exact_mod_cast hC.ne'
  field_simp

lemma shiftedEntropy_sub_eq_conditional (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (r : ℝ) (hr : 0 < r) (C : ℕ) (hC : 0 < C) (t : ℝ) :
    shiftedEntropy μ hμ r hr t -
      shiftedEntropy μ hμ ((C : ℝ) * r) (mul_pos (Nat.cast_pos.mpr hC) hr) t =
        conditionalEntropy (law μ r t) (law_support_finite μ hμ hr t)
          (fun k : ℤ ↦ k / (C : ℤ)) := by
  simpa only [shiftedEntropy, law_map_div] using
    (conditionalEntropy_eq_entropy_sub (law μ r t) (law_support_finite μ hμ hr t)
      (fun k : ℤ ↦ k / (C : ℤ))).symm

lemma intervalIntegrable_scaleConditional (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (r : ℝ) (hr : 0 < r) (C : ℕ) (hC : 0 < C)
    (u v : ℝ) :
    IntervalIntegrable (fun t ↦ conditionalEntropy (law μ r t)
      (law_support_finite μ hμ hr t) (fun k : ℤ ↦ k / (C : ℤ))) volume u v := by
  simp_rw [← shiftedEntropy_sub_eq_conditional μ hμ r hr C hC]
  exact (intervalIntegrable_shiftedEntropy μ hμ r hr u v).sub
    (intervalIntegrable_shiftedEntropy μ hμ _ (mul_pos (Nat.cast_pos.mpr hC) hr) u v)

/-- The entropy difference is the average of the fine label conditioned on the coarse label. -/
lemma entropyBetween_nat_mul_eq_conditional (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (r : ℝ) (hr : 0 < r) (C : ℕ) (hC : 0 < C) :
    entropyBetween μ hμ r hr ((C : ℝ) * r) (mul_pos (Nat.cast_pos.mpr hC) hr) =
      (∫ t in (0 : ℝ)..(C : ℝ) * r, conditionalEntropy (law μ r t)
        (law_support_finite μ hμ hr t) (fun k : ℤ ↦ k / (C : ℤ))) / ((C : ℝ) * r) := by
  rw [entropyBetween, entropy_eq_average_nat_mul μ hμ r hr C hC]
  simp_rw [← shiftedEntropy_sub_eq_conditional μ hμ r hr C hC]
  rw [intervalIntegral.integral_sub (intervalIntegrable_shiftedEntropy μ hμ r hr _ _)
    (intervalIntegrable_shiftedEntropy μ hμ _ (mul_pos (Nat.cast_pos.mpr hC) hr) _ _)]
  simp only [entropy, sub_div]

end ExactOverlaps.ScaleEntropy
