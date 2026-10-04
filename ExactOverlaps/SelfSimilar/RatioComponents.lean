module

public import ExactOverlaps.SelfSimilar.RatioEntropy
public import ExactOverlaps.SelfSimilar.OneSidedComponents

/-!
The mean fine entropy of convolutions after conditioning first on the signed
ratio and then on a coarse translation cell. Conditional entropy concavity
controls its excess over the entropy of the scaled stationary tail.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators

namespace ExactOverlaps.Entropy

theorem dyadicEntropy_right_le_averageRawLeftConvolutionEntropy_add
    (μ ν : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ) (hν : HasBoundedSupport ν)
    (i : ℤ) (m : ℕ) :
    dyadicEntropy ν hν (i + m) ≤
      averageRawLeftConvolutionEntropy μ ν hμ hν i m + Real.log 2 := by
  let : Fintype (dyadicLaw μ i).support := (dyadicLaw_support_finite μ hμ i).fintype
  let p := supportLaw (dyadicLaw μ i)
  have h := Finset.sum_le_sum (s := Finset.univ) (fun k _ ↦
    mul_le_mul_of_nonneg_left
      (dyadicEntropy_right_le_convolution_add_log_two (rawComponent μ i k) ν
        (rawComponent_hasBoundedSupport μ i k) hν (i + m))
      (show 0 ≤ (p k).toReal from ENNReal.toReal_nonneg))
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, sum_pmf_toReal, one_mul] at h
  exact h

end ExactOverlaps.Entropy

namespace ExactOverlaps.SelfSimilar.System

open Entropy
variable {ι : Type*} [Fintype ι]

noncomputable def averageRatioComponentConvolutionEntropy (S : System ι)
    (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ) (n : ℕ) (i : ℤ) (m : ℕ) : ℝ :=
  letI : Fintype (S.wordRatioLaw n).support := (S.wordRatioLaw_support_finite n).fintype
  ∑ r : (S.wordRatioLaw n).support, (S.wordRatioLaw n r).toReal *
    averageRawLeftConvolutionEntropy (S.ratioTranslationProbability n r)
      (S.ratioScaledProbability μ n r) (S.ratioTranslationProbability_hasBoundedSupport n r)
      (S.ratioScaledProbability_hasBoundedSupport μ hμ n r) i m

noncomputable def averageRatioScaledEntropy (S : System ι)
    (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ) (n : ℕ) (i : ℤ) : ℝ :=
  letI : Fintype (S.wordRatioLaw n).support := (S.wordRatioLaw_support_finite n).fintype
  ∑ r : (S.wordRatioLaw n).support, (S.wordRatioLaw n r).toReal *
    dyadicEntropy (S.ratioScaledProbability μ n r)
      (S.ratioScaledProbability_hasBoundedSupport μ hμ n r) i

theorem averageRatioComponentConvolutionEntropy_le (S : System ι)
    (μ : ProbabilityMeasure ℝ) (hμ : S.IsStationary (μ : Measure ℝ))
    (n : ℕ) (i : ℤ) (m : ℕ) :
    S.averageRatioComponentConvolutionEntropy μ (S.hasBoundedSupport hμ) n i m ≤
      dyadicEntropy μ (S.hasBoundedSupport hμ) (i + m) - dyadicEntropy μ (S.hasBoundedSupport hμ) i +
      S.averageRatioScaledEntropy μ (S.hasBoundedSupport hμ) n i + Real.log 2 := by
  let : Fintype (S.wordRatioLaw n).support := (S.wordRatioLaw_support_finite n).fintype
  let p := supportLaw (S.wordRatioLaw n)
  have h := Finset.sum_le_sum (s := Finset.univ) (fun r _ ↦
    mul_le_mul_of_nonneg_left
      (averageRawLeftConvolutionEntropy_le (S.ratioTranslationProbability n r)
        (S.ratioScaledProbability μ n r) (S.ratioTranslationProbability_hasBoundedSupport n r)
        (S.ratioScaledProbability_hasBoundedSupport μ (S.hasBoundedSupport hμ) n r) i m)
      (show 0 ≤ (p r).toReal from ENNReal.toReal_nonneg))
  have hc := S.average_ratioConvolution_increment_le μ hμ n i m
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, sum_pmf_toReal, one_mul] at h
  change S.averageRatioComponentConvolutionEntropy μ (S.hasBoundedSupport hμ) n i m ≤
    (∑ r, (p r).toReal *
      (dyadicEntropy (S.ratioConvolutionProbability μ n r) _ (i + m) -
        dyadicEntropy (S.ratioConvolutionProbability μ n r) _ i)) +
      S.averageRatioScaledEntropy μ (S.hasBoundedSupport hμ) n i + Real.log 2 at h
  exact h.trans (add_le_add (add_le_add hc le_rfl) le_rfl)

theorem averageRatioScaledEntropy_le_componentConvolution_add (S : System ι)
    (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ) (n : ℕ) (i : ℤ) (m : ℕ) :
    S.averageRatioScaledEntropy μ hμ n (i + m) ≤
      S.averageRatioComponentConvolutionEntropy μ hμ n i m + Real.log 2 := by
  let : Fintype (S.wordRatioLaw n).support := (S.wordRatioLaw_support_finite n).fintype
  let p := supportLaw (S.wordRatioLaw n)
  have h := Finset.sum_le_sum (s := Finset.univ) (fun r _ ↦
    mul_le_mul_of_nonneg_left
      (dyadicEntropy_right_le_averageRawLeftConvolutionEntropy_add
        (S.ratioTranslationProbability n r) (S.ratioScaledProbability μ n r)
        (S.ratioTranslationProbability_hasBoundedSupport n r)
        (S.ratioScaledProbability_hasBoundedSupport μ hμ n r) i m)
      (show 0 ≤ (p r).toReal from ENNReal.toReal_nonneg))
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, sum_pmf_toReal, one_mul] at h
  exact h

end ExactOverlaps.SelfSimilar.System
