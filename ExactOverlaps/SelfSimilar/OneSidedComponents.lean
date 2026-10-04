module

public import ExactOverlaps.Entropy.ComponentMixture
public import ExactOverlaps.Entropy.ConvolutionMixture
public import ExactOverlaps.Entropy.ConvolutionBounds
public import ExactOverlaps.Entropy.Atomicity

/-!
Decomposing only the translation factor into coarse dyadic cells leaves the
self-similar tail unchanged. This is the convolution decomposition used in
the nonuniform contraction argument.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators

namespace ExactOverlaps.Entropy

theorem realConvolution_eq_left_mixture {α : Type*} [Fintype α]
    (p : PMF α) (μs : α → ProbabilityMeasure ℝ) (μ ν : ProbabilityMeasure ℝ)
    (hmix : (μ : Measure ℝ) = ∑ a, p a • (μs a : Measure ℝ)) :
    (realConvolution μ ν : Measure ℝ) =
      ∑ a, p a • (realConvolution (μs a) ν : Measure ℝ) := by
  simp only [realConvolution_toMeasure]
  rw [hmix, measure_finset_sum_conv]
  simp only [Measure.conv_smul_left]

theorem realConvolution_eq_rawLeft_mixture (μ ν : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) :
    (realConvolution μ ν : Measure ℝ) =
      (letI : Fintype (dyadicLaw μ i).support := (dyadicLaw_support_finite μ hμ i).fintype
      ∑ k : (dyadicLaw μ i).support, (dyadicLaw μ i) k •
        (realConvolution (rawComponent μ i k) ν : Measure ℝ)) := by
  let : Fintype (dyadicLaw μ i).support := (dyadicLaw_support_finite μ hμ i).fintype
  exact realConvolution_eq_left_mixture (supportLaw (dyadicLaw μ i))
    (rawComponent μ i) μ ν (measure_eq_rawComponent_mixture μ hμ i)

lemma dyadicEntropy_rawComponent_coarse (μ : ProbabilityMeasure ℝ) (i : ℤ)
    (k : (dyadicLaw μ i).support) :
    dyadicEntropy (rawComponent μ i k) (rawComponent_hasBoundedSupport μ i k) i = 0 := by
  have he := dyadicEntropy_rescaledComponent μ i k 0
  simp only [Nat.cast_zero, add_zero] at he
  rw [← he]
  exact dyadicEntropy_zero_of_unit_support _ _ (ae_rescaledComponent_mem_Ico μ i k)

noncomputable def averageRawLeftConvolutionEntropy (μ ν : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (hν : HasBoundedSupport ν) (i : ℤ) (m : ℕ) : ℝ :=
  letI : Fintype (dyadicLaw μ i).support := (dyadicLaw_support_finite μ hμ i).fintype
  ∑ k : (dyadicLaw μ i).support, ((dyadicLaw μ i) k).toReal *
    dyadicEntropy (realConvolution (rawComponent μ i k) ν)
      (realConvolution_hasBoundedSupport _ _ (rawComponent_hasBoundedSupport μ i k) hν) (i + m)

theorem averageRawLeftConvolutionEntropy_le (μ ν : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (hν : HasBoundedSupport ν) (i : ℤ) (m : ℕ) :
    averageRawLeftConvolutionEntropy μ ν hμ hν i m ≤
      dyadicEntropy (realConvolution μ ν) (realConvolution_hasBoundedSupport μ ν hμ hν) (i + m) -
        dyadicEntropy (realConvolution μ ν) (realConvolution_hasBoundedSupport μ ν hμ hν) i +
          dyadicEntropy ν hν i + Real.log 2 := by
  let : Fintype (dyadicLaw μ i).support := (dyadicLaw_support_finite μ hμ i).fintype
  let p := supportLaw (dyadicLaw μ i)
  let H (k : (dyadicLaw μ i).support) (l : ℤ) :=
    dyadicEntropy (realConvolution (rawComponent μ i k) ν)
      (realConvolution_hasBoundedSupport _ _ (rawComponent_hasBoundedSupport μ i k) hν) l
  have h := average_dyadicEntropy_increment_le_of_measure_eq p
    (fun k ↦ realConvolution (rawComponent μ i k) ν)
    (fun k ↦ realConvolution_hasBoundedSupport _ _ (rawComponent_hasBoundedSupport μ i k) hν)
    (realConvolution μ ν) (realConvolution_hasBoundedSupport μ ν hμ hν)
    (realConvolution_eq_rawLeft_mixture μ ν hμ i) i m
  have hc : (∑ k, (p k).toReal * H k i) ≤ dyadicEntropy ν hν i + Real.log 2 := by
    calc
      _ ≤ ∑ k, (p k).toReal * (dyadicEntropy ν hν i + Real.log 2) := by
        apply Finset.sum_le_sum
        intro k _
        apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
        have hcoarse := dyadicEntropy_convolution_le_add_log_two (rawComponent μ i k) ν
          (rawComponent_hasBoundedSupport μ i k) hν i
        simpa only [dyadicEntropy_rawComponent_coarse, zero_add] using hcoarse
      _ = _ := by rw [← Finset.sum_mul, sum_pmf_toReal, one_mul]
  change (∑ k, (p k).toReal * (H k (i + m) - H k i)) ≤ _ at h
  simp only [mul_sub, Finset.sum_sub_distrib] at h
  change (∑ k, (p k).toReal * H k (i + m)) ≤ _
  linarith

end ExactOverlaps.Entropy
