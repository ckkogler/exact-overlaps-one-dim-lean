module

public import ExactOverlaps.SelfSimilar.StationaryApproximation
public import ExactOverlaps.SelfSimilar.ContractionScale

/-!
At the scale of a uniform contraction bound, stationary and finite-word
translation entropies differ by a constant. Their difference per letter
therefore tends to zero. This does not assert exact dimensionality or the
stronger Lyapunov-scale approximation for nonuniform contraction factors.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι]

theorem exists_stationary_entropy_error_bound (S : System ι)
    (ν : ProbabilityMeasure ℝ) (hν : S.IsStationary (ν : Measure ℝ))
    {c : ℝ} (hc : 0 < c) (hmax : ∀ j, |(S.map j).ratio| ≤ c) :
    ∃ C : ℝ, ∀ n : ℕ,
      |Entropy.dyadicEntropy ν (S.hasBoundedSupport hν) (contractionScale c n) -
        Entropy.dyadicEntropy (S.wordTranslationProbability n)
          (S.wordTranslationProbability_hasBoundedSupport n) (contractionScale c n)| ≤ C := by
  obtain ⟨R, hRpos, hR⟩ := S.exists_closedBall_full_measure hν
  obtain ⟨K, hK⟩ := exists_nat_ge R
  have htail : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ R := by
    have hball : ∀ᵐ x ∂(ν : Measure ℝ), x ∈ Metric.closedBall (0 : ℝ) R :=
      ae_iff.mpr hR
    filter_upwards [hball] with x hx
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hx
  refine ⟨Real.log (2 * K + 3 : ℝ), fun n ↦ ?_⟩
  apply S.abs_dyadicEntropy_sub_wordTranslation_le ν hν hc.le hmax htail
  calc
    (2 : ℝ) ^ contractionScale c n * (c ^ n * R) =
        ((2 : ℝ) ^ contractionScale c n * c ^ n) * R := (mul_assoc _ _ _).symm
    _ ≤ 1 * R := mul_le_mul_of_nonneg_right (contractionScale_mul_pow_le_one hc n) hRpos.le
    _ ≤ K := by simpa using hK

/-- Coarse finite-word approximation has vanishing entropy error per letter. -/
theorem stationary_entropy_error_div_tendsto_zero (S : System ι)
    (ν : ProbabilityMeasure ℝ) (hν : S.IsStationary (ν : Measure ℝ))
    {c : ℝ} (hc : 0 < c) (hmax : ∀ j, |(S.map j).ratio| ≤ c) :
    Tendsto (fun n : ℕ ↦
      (Entropy.dyadicEntropy ν (S.hasBoundedSupport hν) (contractionScale c n) -
        Entropy.dyadicEntropy (S.wordTranslationProbability n)
          (S.wordTranslationProbability_hasBoundedSupport n) (contractionScale c n)) / n)
      atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := S.exists_stationary_entropy_error_bound ν hν hc hmax
  apply tendsto_bdd_div_atTop_nhds_zero
    (Eventually.of_forall fun n ↦ (abs_le.mp (hC n)).1)
    (Eventually.of_forall fun n ↦ (abs_le.mp (hC n)).2)
    tendsto_natCast_atTop_atTop

end ExactOverlaps.SelfSimilar.System
