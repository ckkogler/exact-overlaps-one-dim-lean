/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.ScaleEntropy.Averaged

/-!
# Concavity of entropy between integer-related scales

The mixture hypothesis identifies actual Borel probability measures. Its
quantized law is the corresponding PMF mixture, so concavity of conditional
entropy applies before averaging over the common physical translation period.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ExactOverlaps.ScaleEntropy

open Entropy

lemma law_eq_bind_of_measure_eq {ι : Type*} [Fintype ι] (p : PMF ι)
    (ν : ι → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (hmix : (μ : Measure ℝ) = ∑ i, p i • (ν i : Measure ℝ)) (r t : ℝ) :
    law μ r t = p.bind (fun i ↦ law (ν i) r t) := by
  ext k
  simp only [law_apply, hmix, Measure.finsetSum_apply, Measure.smul_apply,
    smul_eq_mul, PMF.bind_apply, tsum_fintype]

lemma average_scaleConditional_le {ι : Type*} [Fintype ι] (p : PMF ι)
    (ν : ι → ProbabilityMeasure ℝ) (hν : ∀ i, HasBoundedSupport (ν i))
    (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ)
    (hmix : (μ : Measure ℝ) = ∑ i, p i • (ν i : Measure ℝ))
    (r : ℝ) (hr : 0 < r) (C : ℕ) (t : ℝ) :
    (∑ i, (p i).toReal * conditionalEntropy (law (ν i) r t)
      (law_support_finite (ν i) (hν i) hr t) (fun k : ℤ ↦ k / (C : ℤ))) ≤
        conditionalEntropy (law μ r t) (law_support_finite μ hμ hr t)
          (fun k : ℤ ↦ k / (C : ℤ)) := by
  have h := average_conditionalEntropy_le_bind p (fun i ↦ law (ν i) r t)
    (fun i ↦ law_support_finite (ν i) (hν i) hr t) (fun k : ℤ ↦ k / (C : ℤ))
  simpa only [← law_eq_bind_of_measure_eq p ν μ hmix r t] using h

/-- Concavity between integer-related scales, for every finite mixture of bounded laws. -/
theorem entropyBetween_mixture_le {ι : Type*} [Fintype ι] (p : PMF ι)
    (ν : ι → ProbabilityMeasure ℝ) (hν : ∀ i, HasBoundedSupport (ν i))
    (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ)
    (hmix : (μ : Measure ℝ) = ∑ i, p i • (ν i : Measure ℝ))
    (r : ℝ) (hr : 0 < r) (C : ℕ) (hC : 0 < C) :
    (∑ i, (p i).toReal * entropyBetween (ν i) (hν i) r hr ((C : ℝ) * r)
      (mul_pos (Nat.cast_pos.mpr hC) hr)) ≤
        entropyBetween μ hμ r hr ((C : ℝ) * r) (mul_pos (Nat.cast_pos.mpr hC) hr) := by
  have hR : 0 < (C : ℝ) * r := mul_pos (Nat.cast_pos.mpr hC) hr
  have hi (i : ι) := intervalIntegrable_scaleConditional (ν i) (hν i) r hr C hC 0 ((C : ℝ) * r)
  have hsum : IntervalIntegrable (fun t ↦ ∑ i, (p i).toReal *
      conditionalEntropy (law (ν i) r t) (law_support_finite (ν i) (hν i) hr t)
        (fun k : ℤ ↦ k / (C : ℤ))) volume 0 ((C : ℝ) * r) := by
    convert (IntervalIntegrable.sum (s := Finset.univ)
      (fun i _ ↦ (hi i).const_mul (p i).toReal)) using 1
    funext t
    simp only [Finset.sum_apply]
  have h := intervalIntegral.integral_mono_on hR.le hsum
    (intervalIntegrable_scaleConditional μ hμ r hr C hC 0 ((C : ℝ) * r))
    (fun t _ ↦ average_scaleConditional_le p ν hν μ hμ hmix r hr C t)
  rw [intervalIntegral.integral_finsetSum (fun i _ ↦ (hi i).const_mul (p i).toReal)] at h
  simp_rw [intervalIntegral.integral_const_mul] at h
  have hd := div_le_div_of_nonneg_right h hR.le
  simp_rw [entropyBetween_nat_mul_eq_conditional _ _ r hr C hC]
  simpa only [Finset.sum_div, mul_div_assoc] using hd

end ExactOverlaps.ScaleEntropy
