module

public import ExactOverlaps.SelfSimilar.RatioTailBounds
public import ExactOverlaps.SelfSimilar.EntropyLevelLimits

/-!
Averaged tail entropy at a common coarse scale below the typical contraction
level. All class weights are the actual signed ratio probabilities.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology BigOperators Classical

namespace ExactOverlaps.SelfSimilar.System

open Entropy
variable {ι : Type*} [Fintype ι]

theorem averageRatioScaledEntropy_buffered_bound (S : System ι) (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) :
    S.averageRatioScaledEntropy μ hμ n (bufferedRatioLevel S.dyadicLyapunov ε n) ≤
      dyadicEntropy μ hμ 0 + Real.log 5 +
        (dyadicEntropy μ hμ (bufferedRatioLevel S.dyadicLyapunov ε n) + Real.log 5) *
          ((S.wordRatioLaw n).toMeasure (S.atypicalRatioLevelSet ε n)).toReal := by
  apply S.averageRatioScaledEntropy_le_split μ hμ n _ _
    (S.measurableSet_atypicalRatioLevelSet ε n)
  · exact add_nonneg (dyadicEntropy_nonneg _ _ _) (Real.log_nonneg (by norm_num))
  · intro r hr
    have ht : (S.dyadicLyapunov - ε) * n ≤ (ratioLevel r : ℝ) ∧
        (ratioLevel r : ℝ) ≤ (S.dyadicLyapunov + ε) * n := by
      simpa only [atypicalRatioLevelSet, Set.mem_ofPred_eq, not_not] using hr
    apply S.ratioScaledEntropy_below_ratioLevel_le μ hμ n r
    have hb := typical_level_lower_buffer ht.1
    simp only [Int.cast_sub] at hb
    have he : 0 ≤ ε * (n : ℝ) := mul_nonneg hε (Nat.cast_nonneg n)
    exact_mod_cast (show (bufferedRatioLevel S.dyadicLyapunov ε n : ℝ) ≤
      (ratioLevel r : ℝ) by linarith)
  · exact fun r ↦ S.ratioScaledEntropy_le μ hμ n r _

theorem averageRatioScaledEntropy_buffered_div_tendsto_zero (S : System ι)
    (μ : ProbabilityMeasure ℝ) (hμ : S.IsStationary (μ : Measure ℝ))
    {ε : ℝ} (hε : 0 < ε) (hεsmall : 2 * ε < S.dyadicLyapunov) :
    Tendsto (fun n : ℕ ↦ S.averageRatioScaledEntropy μ (S.hasBoundedSupport hμ) n
      (bufferedRatioLevel S.dyadicLyapunov ε n) / n) atTop (𝓝 0) := by
  let C := dyadicEntropy μ (S.hasBoundedSupport hμ) 0 + Real.log 5
  have hi := S.dyadicEntropy_level_div_tendsto_dimension μ hμ (sub_pos.mpr hεsmall)
    (bufferedRatioLevel_div_tendsto S.dyadicLyapunov ε)
  have hbad := S.wordRatioLaw_atypical_level_mass_tendsto_zero hε
  have hupper : Tendsto (fun n : ℕ ↦ C / n +
      (dyadicEntropy μ (S.hasBoundedSupport hμ)
          (bufferedRatioLevel S.dyadicLyapunov ε n) / n + Real.log 5 / n) *
        ((S.wordRatioLaw n).toMeasure (S.atypicalRatioLevelSet ε n)).toReal)
      atTop (𝓝 0) := by
    simpa only [add_zero, mul_zero, zero_add] using
      (tendsto_const_div_atTop_nhds_zero_nat C).add
        ((hi.add (tendsto_const_div_atTop_nhds_zero_nat (Real.log 5))).mul hbad)
  apply squeeze_zero (fun n ↦ div_nonneg
    (S.averageRatioScaledEntropy_nonneg μ (S.hasBoundedSupport hμ) n _)
    (Nat.cast_nonneg n)) _ hupper
  intro n
  have h := div_le_div_of_nonneg_right
    (S.averageRatioScaledEntropy_buffered_bound μ (S.hasBoundedSupport hμ) hε.le n)
    (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  convert h using 1
  dsimp [C]
  ring

end ExactOverlaps.SelfSimilar.System
