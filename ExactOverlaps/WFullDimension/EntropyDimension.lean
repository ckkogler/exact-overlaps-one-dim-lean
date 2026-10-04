/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.ScaleEntropy.DyadicComparison
public import ExactOverlaps.SelfSimilar.DimensionIdentification
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
Maximal entropy increments force dimension one for the actual stationary
measure. Telescoping and Cesaro averaging concern the genuine averaged
mesh entropy; the proved dyadic comparison identifies its limiting rate
with the standard Hausdorff dimension.
-/

@[expose] public section

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace ExactOverlaps.WFullDimension

theorem tendsto_div_nat_of_increment {H : ℕ → ℝ} {L : ℝ}
    (h : Tendsto (fun n ↦ H (n + 1) - H n) atTop (𝓝 L)) :
    Tendsto (fun n ↦ H n / n) atTop (𝓝 L) := by
  have hsum (n : ℕ) : (∑ j ∈ Finset.range n, (H (j + 1) - H j)) = H n - H 0 := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; ring
  have hh := h.cesaro.add (tendsto_const_div_atTop_nhds_zero_nat (H 0))
  simp only [add_zero] at hh
  convert hh using 1
  funext n
  rw [hsum]
  ring

theorem averaged_dyadic_entropy_div_tendsto {ι : Type*} [Fintype ι]
    (S : SelfSimilar.System ι) (μ : ProbabilityMeasure ℝ)
    (hμ : S.IsStationary (μ : Measure ℝ)) :
    Tendsto (fun n : ℕ ↦ ScaleEntropy.entropy μ (S.hasBoundedSupport hμ)
      ((1 / 2 : ℝ) ^ n) (pow_pos (by norm_num) n) / n) atTop
      (𝓝 ((lowerHausdorffDimension (μ : Measure ℝ)).toReal * Real.log 2)) := by
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hd : Tendsto (fun n : ℕ ↦ Entropy.dyadicEntropy μ (S.hasBoundedSupport hμ) n / n)
      atTop (𝓝 ((lowerHausdorffDimension (μ : Measure ℝ)).toReal * Real.log 2)) := by
    have h := (S.normalizedDyadicEntropy_tendsto_dimension μ hμ).mul_const (Real.log 2)
    convert h using 1
    funext n
    simp only [Entropy.normalizedDyadicEntropy, div_mul_eq_div_div, div_mul_cancel₀ _ hlog]
  have he : Tendsto (fun n : ℕ ↦
      (ScaleEntropy.entropy μ (S.hasBoundedSupport hμ) ((1 / 2 : ℝ) ^ n)
        (pow_pos (by norm_num) n) -
        Entropy.dyadicEntropy μ (S.hasBoundedSupport hμ) n) / n) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n ↦ ?_) (tendsto_const_div_atTop_nhds_zero_nat (Real.log 2))
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    simpa only [zpow_neg, zpow_natCast, one_div, inv_pow] using
      ScaleEntropy.abs_entropy_dyadic_sub_le_log_two μ (S.hasBoundedSupport hμ) (n : ℤ)
  convert he.add hd using 1
  · funext n
    ring
  · simp

theorem dimension_toReal_eq_one_of_entropy_increments {ι : Type*} [Fintype ι]
    (S : SelfSimilar.System ι) (μ : ProbabilityMeasure ℝ)
    (hμ : S.IsStationary (μ : Measure ℝ))
    (hinc : Tendsto (fun n : ℕ ↦
      ScaleEntropy.entropy μ (S.hasBoundedSupport hμ) ((1 / 2 : ℝ) ^ (n + 1))
        (pow_pos (by norm_num) (n + 1)) -
      ScaleEntropy.entropy μ (S.hasBoundedSupport hμ) ((1 / 2 : ℝ) ^ n)
        (pow_pos (by norm_num) n)) atTop (𝓝 (Real.log 2))) :
    (lowerHausdorffDimension (μ : Measure ℝ)).toReal = 1 := by
  have h := tendsto_nhds_unique (averaged_dyadic_entropy_div_tendsto S μ hμ)
    (tendsto_div_nat_of_increment hinc)
  exact (mul_right_cancel₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
    (h.trans (one_mul (Real.log 2)).symm))

theorem dimension_eq_one_of_entropy_increments {ι : Type*} [Fintype ι]
    (S : SelfSimilar.System ι) (μ : ProbabilityMeasure ℝ)
    (hμ : S.IsStationary (μ : Measure ℝ))
    (hinc : Tendsto (fun n : ℕ ↦
      ScaleEntropy.entropy μ (S.hasBoundedSupport hμ) ((1 / 2 : ℝ) ^ (n + 1))
        (pow_pos (by norm_num) (n + 1)) -
      ScaleEntropy.entropy μ (S.hasBoundedSupport hμ) ((1 / 2 : ℝ) ^ n)
        (pow_pos (by norm_num) n)) atTop (𝓝 (Real.log 2))) :
    lowerHausdorffDimension (μ : Measure ℝ) = 1 := by
  exact (ENNReal.toReal_eq_one_iff _).mp
    (dimension_toReal_eq_one_of_entropy_increments S μ hμ hinc)

end ExactOverlaps.WFullDimension
