module

public import ExactOverlaps.SelfSimilar.OneSidedComponents

/-!
Translation components may be taken at a finer, ratio-dependent level while
conditional entropy concavity is applied at one common coarse level.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators

namespace ExactOverlaps.Entropy

theorem averageRawLeftConvolutionEntropy_le_at_coarser_level (μ ν : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (hν : HasBoundedSupport ν) {i j : ℤ}
    (hij : i ≤ j) (m : ℕ) :
    averageRawLeftConvolutionEntropy μ ν hμ hν j m ≤
      dyadicEntropy (realConvolution μ ν) (realConvolution_hasBoundedSupport μ ν hμ hν) (j + m) -
        dyadicEntropy (realConvolution μ ν) (realConvolution_hasBoundedSupport μ ν hμ hν) i +
          dyadicEntropy ν hν i + Real.log 2 := by
  let : Fintype (dyadicLaw μ j).support := (dyadicLaw_support_finite μ hμ j).fintype
  let p := supportLaw (dyadicLaw μ j)
  let H (k : (dyadicLaw μ j).support) (l : ℤ) :=
    dyadicEntropy (realConvolution (rawComponent μ j k) ν)
      (realConvolution_hasBoundedSupport _ _ (rawComponent_hasBoundedSupport μ j k) hν) l
  obtain ⟨l, hl⟩ := Int.le.dest hij
  have hlevel : i + ((l + m : ℕ) : ℤ) = j + m := by omega
  have h := average_dyadicEntropy_increment_le_of_measure_eq p
    (fun k ↦ realConvolution (rawComponent μ j k) ν)
    (fun k ↦ realConvolution_hasBoundedSupport _ _ (rawComponent_hasBoundedSupport μ j k) hν)
    (realConvolution μ ν) (realConvolution_hasBoundedSupport μ ν hμ hν)
    (realConvolution_eq_rawLeft_mixture μ ν hμ j) i (l + m)
  rw [hlevel] at h
  have hc : (∑ k, (p k).toReal * H k i) ≤ dyadicEntropy ν hν i + Real.log 2 := by
    calc
      _ ≤ ∑ k, (p k).toReal * (dyadicEntropy ν hν i + Real.log 2) := by
        apply Finset.sum_le_sum
        intro k _
        apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
        have hcoarse := dyadicEntropy_convolution_le_add_log_two (rawComponent μ j k) ν
          (rawComponent_hasBoundedSupport μ j k) hν i
        have hraw := dyadicEntropy_mono (rawComponent μ j k) (rawComponent_hasBoundedSupport μ j k) hij
        rw [dyadicEntropy_rawComponent_coarse] at hraw
        change H k i ≤ _ at hcoarse
        linarith
      _ = _ := by rw [← Finset.sum_mul, sum_pmf_toReal, one_mul]
  change (∑ k, (p k).toReal * (H k (j + m) - H k i)) ≤ _ at h
  simp only [mul_sub, Finset.sum_sub_distrib] at h
  change (∑ k, (p k).toReal * H k (j + m)) ≤ _
  linarith

end ExactOverlaps.Entropy
