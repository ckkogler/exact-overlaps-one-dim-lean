module

public import ExactOverlaps.SelfSimilar.RatioComponents
public import ExactOverlaps.SelfSimilar.CoarseComponentEntropy
public import ExactOverlaps.SelfSimilar.EntropyIncrementComparison

/-!
Ratio-dependent translation components with a common fine scale and a common
buffered conditioning scale. The chosen component levels remain explicit;
no uniform bound on ratios normalized at the buffered level is assumed.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators

namespace ExactOverlaps.SelfSimilar.System

open Entropy
variable {ι : Type*} [Fintype ι]

noncomputable def averageVariableRatioConvolutionEntropy (S : System ι)
    (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ) (n : ℕ)
    (j : (S.wordRatioLaw n).support → ℤ) (f : ℤ) : ℝ :=
  letI : Fintype (S.wordRatioLaw n).support := (S.wordRatioLaw_support_finite n).fintype
  ∑ r : (S.wordRatioLaw n).support, (S.wordRatioLaw n r).toReal *
    averageRawLeftConvolutionEntropy (S.ratioTranslationProbability n r)
      (S.ratioScaledProbability μ n r) (S.ratioTranslationProbability_hasBoundedSupport n r)
      (S.ratioScaledProbability_hasBoundedSupport μ hμ n r) (j r) (f - j r).toNat

noncomputable def averageVariableRatioTranslationEntropy (S : System ι) (n : ℕ)
    (j : (S.wordRatioLaw n).support → ℤ) (f : ℤ) : ℝ :=
  letI : Fintype (S.wordRatioLaw n).support := (S.wordRatioLaw_support_finite n).fintype
  ∑ r : (S.wordRatioLaw n).support, (S.wordRatioLaw n r).toReal *
    averageRawComponentEntropy (S.ratioTranslationProbability n r)
      (S.ratioTranslationProbability_hasBoundedSupport n r) (j r) (f - j r).toNat

theorem averageVariableRatioConvolutionEntropy_le (S : System ι)
    (μ : ProbabilityMeasure ℝ) (hμ : S.IsStationary (μ : Measure ℝ))
    (n : ℕ) (j : (S.wordRatioLaw n).support → ℤ) {i f : ℤ} (hif : i ≤ f)
    (hij : ∀ r, i ≤ j r) (hjf : ∀ r, j r ≤ f) :
    S.averageVariableRatioConvolutionEntropy μ (S.hasBoundedSupport hμ) n j f ≤
      dyadicEntropy μ (S.hasBoundedSupport hμ) f - dyadicEntropy μ (S.hasBoundedSupport hμ) i +
      S.averageRatioScaledEntropy μ (S.hasBoundedSupport hμ) n i + Real.log 2 := by
  let : Fintype (S.wordRatioLaw n).support := (S.wordRatioLaw_support_finite n).fintype
  let p := supportLaw (S.wordRatioLaw n)
  have hlevel (r : (S.wordRatioLaw n).support) : j r + ((f - j r).toNat : ℤ) = f := by
    have := hjf r
    omega
  have hcommon : i + ((f - i).toNat : ℤ) = f := by omega
  have h := Finset.sum_le_sum (s := Finset.univ) (fun r _ ↦
    mul_le_mul_of_nonneg_left
      (averageRawLeftConvolutionEntropy_le_at_coarser_level (S.ratioTranslationProbability n r)
        (S.ratioScaledProbability μ n r) (S.ratioTranslationProbability_hasBoundedSupport n r)
        (S.ratioScaledProbability_hasBoundedSupport μ (S.hasBoundedSupport hμ) n r)
        (hij r) (f - j r).toNat)
      (show 0 ≤ (p r).toReal from ENNReal.toReal_nonneg))
  have hc := S.average_ratioConvolution_increment_le μ hμ n i (f - i).toNat
  simp only [hcommon] at hc
  simp only [hlevel, mul_add, Finset.sum_add_distrib,
    ← Finset.sum_mul, sum_pmf_toReal, one_mul] at h
  change S.averageVariableRatioConvolutionEntropy μ (S.hasBoundedSupport hμ) n j f ≤
    (∑ r, (p r).toReal *
      (dyadicEntropy (S.ratioConvolutionProbability μ n r) _ f -
        dyadicEntropy (S.ratioConvolutionProbability μ n r) _ i)) +
      S.averageRatioScaledEntropy μ (S.hasBoundedSupport hμ) n i + Real.log 2 at h
  exact h.trans (add_le_add (add_le_add hc le_rfl) le_rfl)

theorem averageRatioScaledEntropy_le_variableConvolution_add (S : System ι)
    (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ) (n : ℕ)
    (j : (S.wordRatioLaw n).support → ℤ) (f : ℤ) (hjf : ∀ r, j r ≤ f) :
    S.averageRatioScaledEntropy μ hμ n f ≤
      S.averageVariableRatioConvolutionEntropy μ hμ n j f + Real.log 2 := by
  let : Fintype (S.wordRatioLaw n).support := (S.wordRatioLaw_support_finite n).fintype
  let p := supportLaw (S.wordRatioLaw n)
  have hlevel (r : (S.wordRatioLaw n).support) : j r + ((f - j r).toNat : ℤ) = f := by
    have := hjf r
    omega
  have h := Finset.sum_le_sum (s := Finset.univ) (fun r _ ↦
    mul_le_mul_of_nonneg_left
      (dyadicEntropy_right_le_averageRawLeftConvolutionEntropy_add
        (S.ratioTranslationProbability n r) (S.ratioScaledProbability μ n r)
        (S.ratioTranslationProbability_hasBoundedSupport n r)
        (S.ratioScaledProbability_hasBoundedSupport μ hμ n r) (j r) (f - j r).toNat)
      (show 0 ≤ (p r).toReal from ENNReal.toReal_nonneg))
  simp only [hlevel, mul_add, Finset.sum_add_distrib,
    ← Finset.sum_mul, sum_pmf_toReal, one_mul] at h
  exact h

theorem translation_increment_le_variable_components_add_gap (S : System ι)
    (n : ℕ) (j : (S.wordRatioLaw n).support → ℤ) {i f : ℤ} (hif : i ≤ f)
    (hij : ∀ r, i ≤ j r) (hjf : ∀ r, j r ≤ f) :
    dyadicEntropy (S.wordTranslationProbability n) (S.wordTranslationProbability_hasBoundedSupport n) f -
      dyadicEntropy (S.wordTranslationProbability n) (S.wordTranslationProbability_hasBoundedSupport n) i ≤
    finiteEntropy (S.wordRatioLaw n) (S.wordRatioLaw_support_finite n) +
      S.averageVariableRatioTranslationEntropy n j f +
      (letI : Fintype (S.wordRatioLaw n).support := (S.wordRatioLaw_support_finite n).fintype
      ∑ r : (S.wordRatioLaw n).support, (S.wordRatioLaw n r).toReal *
        ((j r - i : ℤ) : ℝ) * Real.log 2) := by
  let : Fintype (S.wordRatioLaw n).support := (S.wordRatioLaw_support_finite n).fintype
  have hlevel (r : (S.wordRatioLaw n).support) : j r + ((f - j r).toNat : ℤ) = f := by
    have := hjf r
    omega
  have hcommon : i + ((f - i).toNat : ℤ) = f := by omega
  have h := S.translation_increment_le_ratioEntropy_add_average n i (f - i).toNat
  simp only [hcommon] at h
  have hp := Finset.sum_le_sum (s := Finset.univ) (fun r _ ↦
    mul_le_mul_of_nonneg_left
      (dyadicEntropy_increment_le_int (S.ratioTranslationProbability n r)
        (S.ratioTranslationProbability_hasBoundedSupport n r) (hij r))
      (show 0 ≤ (S.wordRatioLaw n r).toReal from ENNReal.toReal_nonneg))
  unfold averageVariableRatioTranslationEntropy
  simp only [averageRawComponentEntropy_eq_sub, hlevel]
  simp only [mul_sub, Finset.sum_sub_distrib, mul_assoc] at h hp ⊢
  linarith

end ExactOverlaps.SelfSimilar.System
