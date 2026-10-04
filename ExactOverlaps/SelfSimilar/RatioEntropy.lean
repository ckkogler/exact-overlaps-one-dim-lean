module

public import ExactOverlaps.SelfSimilar.RatioConvolution
public import ExactOverlaps.SelfSimilar.MixtureEntropyBounds

/-!
Entropy comparisons for the genuine signed-ratio mixtures.
The translation increment differs from its ratio-conditioned average by
at most the entropy of the ratio label, already known to be sublinear.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators

namespace ExactOverlaps.Entropy

theorem finiteEntropy_supportLaw {α : Type*} (p : PMF α) (hp : p.support.Finite) :
    finiteEntropy (supportLaw p) (by let _ := hp.fintype; exact Set.toFinite _) =
      finiteEntropy p hp := by
  have h := finiteEntropy_map_of_injective (supportLaw p)
    (by let _ := hp.fintype; exact Set.toFinite _) Subtype.val_injective
  simpa only [supportLaw_map_val] using h.symm

end ExactOverlaps.Entropy

namespace ExactOverlaps.SelfSimilar.System

open Entropy
variable {ι : Type*} [Fintype ι]

theorem average_ratioTranslation_increment_le (S : System ι) (n : ℕ) (i : ℤ) (m : ℕ) :
    (letI : Fintype (S.wordRatioLaw n).support := (S.wordRatioLaw_support_finite n).fintype
    ∑ r : (S.wordRatioLaw n).support, (S.wordRatioLaw n r).toReal *
      (dyadicEntropy (S.ratioTranslationProbability n r)
          (S.ratioTranslationProbability_hasBoundedSupport n r) (i + m) -
        dyadicEntropy (S.ratioTranslationProbability n r)
          (S.ratioTranslationProbability_hasBoundedSupport n r) i)) ≤
      dyadicEntropy (S.wordTranslationProbability n)
          (S.wordTranslationProbability_hasBoundedSupport n) (i + m) -
        dyadicEntropy (S.wordTranslationProbability n)
          (S.wordTranslationProbability_hasBoundedSupport n) i := by
  let : Fintype (S.wordRatioLaw n).support := (S.wordRatioLaw_support_finite n).fintype
  exact average_dyadicEntropy_increment_le_of_measure_eq (supportLaw (S.wordRatioLaw n))
    (S.ratioTranslationProbability n) (S.ratioTranslationProbability_hasBoundedSupport n)
    (S.wordTranslationProbability n) (S.wordTranslationProbability_hasBoundedSupport n)
    (S.wordTranslationProbability_eq_ratio_mixture n) i m

theorem translation_increment_le_ratioEntropy_add_average (S : System ι)
    (n : ℕ) (i : ℤ) (m : ℕ) :
    dyadicEntropy (S.wordTranslationProbability n)
        (S.wordTranslationProbability_hasBoundedSupport n) (i + m) -
      dyadicEntropy (S.wordTranslationProbability n)
        (S.wordTranslationProbability_hasBoundedSupport n) i ≤
    finiteEntropy (S.wordRatioLaw n) (S.wordRatioLaw_support_finite n) +
      (letI : Fintype (S.wordRatioLaw n).support := (S.wordRatioLaw_support_finite n).fintype
      ∑ r : (S.wordRatioLaw n).support, (S.wordRatioLaw n r).toReal *
        (dyadicEntropy (S.ratioTranslationProbability n r)
            (S.ratioTranslationProbability_hasBoundedSupport n r) (i + m) -
          dyadicEntropy (S.ratioTranslationProbability n r)
            (S.ratioTranslationProbability_hasBoundedSupport n r) i)) := by
  let : Fintype (S.wordRatioLaw n).support := (S.wordRatioLaw_support_finite n).fintype
  have h := dyadicEntropy_increment_le_label_add_average_of_measure_eq
    (supportLaw (S.wordRatioLaw n)) (S.ratioTranslationProbability n)
    (S.ratioTranslationProbability_hasBoundedSupport n)
    (S.wordTranslationProbability n) (S.wordTranslationProbability_hasBoundedSupport n)
    (S.wordTranslationProbability_eq_ratio_mixture n) i m
  simpa only [finiteEntropy_supportLaw (S.wordRatioLaw n) (S.wordRatioLaw_support_finite n),
    supportLaw_apply] using h

theorem average_ratioConvolution_increment_le (S : System ι)
    (μ : ProbabilityMeasure ℝ) (hμ : S.IsStationary (μ : Measure ℝ))
    (n : ℕ) (i : ℤ) (m : ℕ) :
    (letI : Fintype (S.wordRatioLaw n).support := (S.wordRatioLaw_support_finite n).fintype
    ∑ r : (S.wordRatioLaw n).support, (S.wordRatioLaw n r).toReal *
      (dyadicEntropy (S.ratioConvolutionProbability μ n r)
          (S.ratioConvolutionProbability_hasBoundedSupport μ (S.hasBoundedSupport hμ) n r) (i + m) -
        dyadicEntropy (S.ratioConvolutionProbability μ n r)
          (S.ratioConvolutionProbability_hasBoundedSupport μ (S.hasBoundedSupport hμ) n r) i)) ≤
      dyadicEntropy μ (S.hasBoundedSupport hμ) (i + m) -
        dyadicEntropy μ (S.hasBoundedSupport hμ) i := by
  let : Fintype (S.wordRatioLaw n).support := (S.wordRatioLaw_support_finite n).fintype
  exact average_dyadicEntropy_increment_le_of_measure_eq (supportLaw (S.wordRatioLaw n))
    (S.ratioConvolutionProbability μ n)
    (S.ratioConvolutionProbability_hasBoundedSupport μ (S.hasBoundedSupport hμ) n)
    μ (S.hasBoundedSupport hμ) (S.stationary_eq_ratio_convolution_mixture μ hμ n) i m

end ExactOverlaps.SelfSimilar.System
