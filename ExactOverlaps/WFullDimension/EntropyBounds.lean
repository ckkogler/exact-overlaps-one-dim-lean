/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.ScaleEntropy.Averaged
public import ExactOverlaps.SelfSimilar.EntropyComparison
public import Mathlib.Data.Int.Interval

/-! Sharp bounds for entropy between a mesh and twice that mesh. -/

@[expose] public section

noncomputable section
open MeasureTheory Set

namespace ExactOverlaps.WFullDimension

open Entropy ScaleEntropy

lemma conditionalEntropy_div_two_bounds (p : PMF ℤ) (hp : p.support.Finite) :
    0 ≤ conditionalEntropy p hp (fun k ↦ k / 2) ∧
      conditionalEntropy p hp (fun k ↦ k / 2) ≤ Real.log 2 := by
  classical
  refine ⟨conditionalEntropy_nonneg p hp _, ?_⟩
  apply conditionalEntropy_le_log_of_card_le p hp (fun k ↦ k / 2) (N := 2)
  intro b
  have hsub : (conditionalPMF_support_finite p hp (fun k ↦ k / 2) b).toFinset ⊆
      Finset.Icc (2 * (b : ℤ)) (2 * (b : ℤ) + 1) := by
    intro k hk
    have he : k / 2 = (b : ℤ) := by
      have hmem : k ∈ (conditionalPMF p (fun k ↦ k / 2) b).support := by simpa using hk
      exact (conditionalPMF_support p (fun k ↦ k / 2) b ▸ hmem).1
    simp only [Finset.mem_Icc]
    omega
  apply (Finset.card_le_card hsub).trans_eq
  rw [Int.card_Icc]
  have he : 2 * (b : ℤ) + 1 + 1 - 2 * (b : ℤ) = 2 := by omega
  rw [he]
  rfl

theorem entropyBetween_double_bounds (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (r : ℝ) (hr : 0 < r) :
    0 ≤ entropyBetween μ hμ r hr (2 * r) (by positivity) ∧
      entropyBetween μ hμ r hr (2 * r) (by positivity) ≤ Real.log 2 := by
  have hR : 0 < (2 : ℝ) * r := by positivity
  have hi := intervalIntegrable_scaleConditional μ hμ r hr 2 (by norm_num) 0 (2 * r)
  have hB (t : ℝ) := conditionalEntropy_div_two_bounds (law μ r t)
    (law_support_finite μ hμ hr t)
  have he := entropyBetween_nat_mul_eq_conditional μ hμ r hr 2 (by norm_num)
  norm_num only [Nat.cast_ofNat] at he hi
  rw [he]
  constructor
  · exact div_nonneg (intervalIntegral.integral_nonneg_of_forall hR.le
      (fun t ↦ (hB t).1)) hR.le
  · have hh := intervalIntegral.integral_mono_on hR.le hi intervalIntegrable_const
      (fun t _ ↦ (hB t).2)
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hh
    exact (div_le_iff₀ hR).mpr (by nlinarith [hh])

end ExactOverlaps.WFullDimension
