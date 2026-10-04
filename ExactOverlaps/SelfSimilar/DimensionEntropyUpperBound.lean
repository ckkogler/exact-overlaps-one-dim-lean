module

public import ExactOverlaps.SelfSimilar.HochmanFineEntropy
public import ExactOverlaps.SelfSimilar.RandomWalkTranslationEntropy

/-!
The standard upper bound by ambient and random-walk entropy dimension.
The entropy-rate bound follows from the proved coarse-scale approximation
and ordinary data processing, independently of the final dimension formula.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ExactOverlaps.SelfSimilar.System

open Entropy
variable {ι : Type*} [Fintype ι]

theorem dyadicEntropy_wordTranslation_le (S : System ι) (n : ℕ) (i : ℤ) :
    dyadicEntropy (S.wordTranslationProbability n) (S.wordTranslationProbability_hasBoundedSupport n) i ≤
      finiteEntropy (S.wordTranslationLaw n) (S.wordTranslationLaw_support_finite n) := by
  have he := dyadicLaw_eq_map_of_toMeasure_eq (S.wordTranslationProbability n)
    (S.wordTranslationLaw n) rfl i
  have h := finiteEntropy_map_le (S.wordTranslationLaw n) (S.wordTranslationLaw_support_finite n)
    (dyadicQuantize i)
  simpa only [← he, dyadicEntropy] using h

theorem dimension_le_entropyRate_div_lyapunov (S : System ι)
    (μ : ProbabilityMeasure ℝ) (hμ : S.IsStationary (μ : Measure ℝ)) :
    (lowerHausdorffDimension (μ : Measure ℝ)).toReal ≤ S.randomWalkEntropyRate / |S.lyapunov| := by
  have hb := le_of_tendsto_of_tendsto'
    (S.wordTranslationEntropy_coarse_div_tendsto μ hμ)
    S.wordTranslationLaw_entropy_div_tendsto_rate
    (fun n ↦ div_le_div_of_nonneg_right
      (S.dyadicEntropy_wordTranslation_le n (targetRatioLevel S.dyadicLyapunov 1 n))
      (Nat.cast_nonneg n))
  apply (le_div_iff₀ S.abs_lyapunov_pos).mpr
  simpa only [S.abs_lyapunov_eq_neg, mul_comm] using hb

theorem dimension_le_min_entropyRate (S : System ι)
    (μ : ProbabilityMeasure ℝ) (hμ : S.IsStationary (μ : Measure ℝ)) :
    (lowerHausdorffDimension (μ : Measure ℝ)).toReal ≤
      min 1 (S.randomWalkEntropyRate / |S.lyapunov|) := by
  refine le_min ?_ (S.dimension_le_entropyRate_div_lyapunov μ hμ)
  have h := ENNReal.toReal_mono ENNReal.one_ne_top (lowerHausdorffDimension_le_one (μ : Measure ℝ))
  simpa only [ENNReal.toReal_one] using h

end ExactOverlaps.SelfSimilar.System
