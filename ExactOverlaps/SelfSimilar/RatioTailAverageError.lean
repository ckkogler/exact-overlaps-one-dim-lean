module

public import ExactOverlaps.SelfSimilar.RatioTailBounds

/-! Exact weighted error bounds after splitting the genuine ratio classes. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators Classical

namespace ExactOverlaps.SelfSimilar.System

open Entropy
variable {ι : Type*} [Fintype ι]

theorem averageRatioScaledEntropy_error_le_split (S : System ι) (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (n : ℕ) (i : ℤ) (T : ℝ)
    (E : Set ℝ) (hE : MeasurableSet E) {C B : ℝ} (hC : 0 ≤ C)
    (hgood : ∀ r : (S.wordRatioLaw n).support, (r : ℝ) ∉ E →
      |dyadicEntropy (S.ratioScaledProbability μ n r)
        (S.ratioScaledProbability_hasBoundedSupport μ hμ n r) i / n - T| ≤ C)
    (hall : ∀ r : (S.wordRatioLaw n).support,
      |dyadicEntropy (S.ratioScaledProbability μ n r)
        (S.ratioScaledProbability_hasBoundedSupport μ hμ n r) i / n - T| ≤ B) :
    |S.averageRatioScaledEntropy μ hμ n i / n - T| ≤ C +
      B * ((S.wordRatioLaw n).toMeasure E).toReal := by
  let : Fintype (S.wordRatioLaw n).support := (S.wordRatioLaw_support_finite n).fintype
  let p := supportLaw (S.wordRatioLaw n)
  let F (r : (S.wordRatioLaw n).support) :=
    dyadicEntropy (S.ratioScaledProbability μ n r)
      (S.ratioScaledProbability_hasBoundedSupport μ hμ n r) i / n - T
  have he : S.averageRatioScaledEntropy μ hμ n i / n - T = ∑ r, (p r).toReal * F r := by
    change (∑ r, (p r).toReal * dyadicEntropy (S.ratioScaledProbability μ n r) _ i) / n - T = _
    simp only [F, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, sum_pmf_toReal, one_mul]
    congr 1
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro r _
    ring
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun r _ ↦ show
      (p r).toReal * |F r| ≤ (p r).toReal * C +
        B * (if (r : ℝ) ∈ E then (p r).toReal else 0) from by
    have hw : 0 ≤ (p r).toReal := ENNReal.toReal_nonneg
    by_cases hr : (r : ℝ) ∈ E
    · simp only [ite_eq_left hr]
      have hb := mul_le_mul_of_nonneg_left (hall r) hw
      have hc := mul_nonneg hw hC
      change (p r).toReal * |F r| ≤ _ at hb
      nlinarith
    · simp only [ite_eq_right hr, mul_zero, add_zero]
      exact mul_le_mul_of_nonneg_left (hgood r hr) hw)
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    sum_pmf_toReal, one_mul] at hs
  rw [he, S.wordRatioLaw_mass_eq_support_sum n E hE]
  calc
    _ ≤ ∑ r, |(p r).toReal * F r| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ r, (p r).toReal * |F r| := by
      apply Finset.sum_congr rfl
      intro r _
      rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    _ ≤ _ := by simpa only [p, supportLaw_apply] using hs

end ExactOverlaps.SelfSimilar.System
