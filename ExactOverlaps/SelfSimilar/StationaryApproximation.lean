module

public import ExactOverlaps.SelfSimilar.StationaryCoupling
public import ExactOverlaps.SelfSimilar.EntropyBridge
public import ExactOverlaps.SelfSimilar.QuantizedCoupling

/-!
The translation law of a finite random composition approximates the stationary
measure at every mesh wider than the remaining tail. The proof uses a genuine
coupling, so it permits overlaps, zero branch weights, signed multipliers, and
atoms on dyadic boundaries.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι]

/-- The finite translation law, regarded as a Borel probability measure. -/
noncomputable def wordTranslationProbability (S : System ι) (n : ℕ) :
    ProbabilityMeasure ℝ :=
  (S.wordTranslationLaw n).toMeasure.toProbabilityMeasure

theorem wordTranslationProbability_hasBoundedSupport (S : System ι) (n : ℕ) :
    Entropy.HasBoundedSupport (S.wordTranslationProbability n) := by
  obtain ⟨B, _, hB⟩ := S.exists_uniform_translation_bound
  refine ⟨-B, B, ?_⟩
  change Icc (-B) B ∈ ae (S.wordTranslationLaw n).toMeasure
  rw [mem_ae_iff_prob_eq_one measurableSet_Icc]
  apply (PMF.toMeasure_apply_eq_one_iff _ measurableSet_Icc).mpr
  intro b hb
  exact abs_le.mp (hB n b hb)

theorem wordCoupling_map_fst_probability (S : System ι) (ν : ProbabilityMeasure ℝ)
    (n : ℕ) : (S.wordCoupling ν n).map Prod.fst = S.wordTranslationProbability n := by
  apply ProbabilityMeasure.toMeasure_injective
  exact S.wordCoupling_map_fst ν n

/-- Entropy error at a scale where the stationary tail spans at most K cells. -/
theorem abs_dyadicEntropy_sub_wordTranslation_le (S : System ι)
    (ν : ProbabilityMeasure ℝ) (hν : S.IsStationary (ν : Measure ℝ))
    {c R : ℝ} (hc : 0 ≤ c) (hmax : ∀ j, |(S.map j).ratio| ≤ c)
    (hR : ∀ᵐ z ∂(ν : Measure ℝ), |z| ≤ R)
    (n : ℕ) (i : ℤ) (K : ℕ) (hscale : (2 : ℝ) ^ i * (c ^ n * R) ≤ K) :
    |Entropy.dyadicEntropy ν (S.hasBoundedSupport hν) i -
      Entropy.dyadicEntropy (S.wordTranslationProbability n)
        (S.wordTranslationProbability_hasBoundedSupport n) i| ≤ Real.log (2 * K + 3 : ℝ) := by
  have hfst := S.wordCoupling_map_fst_probability ν n
  have hsnd := S.wordCoupling_map_snd ν hν n
  have hX : Entropy.HasBoundedSupport ((S.wordCoupling ν n).map Prod.fst) := by
    rw [hfst]
    exact S.wordTranslationProbability_hasBoundedSupport n
  have hY : Entropy.HasBoundedSupport ((S.wordCoupling ν n).map Prod.snd) := by
    rw [hsnd]
    exact S.hasBoundedSupport hν
  have hdisp : ∀ᵐ z ∂(S.wordCoupling ν n : Measure (ℝ × ℝ)),
      |(2 : ℝ) ^ i * (z.2 - z.1)| ≤ K := by
    filter_upwards [S.wordCoupling_displacement ν hc hmax hR n] with z hz
    rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) i)]
    exact (mul_le_mul_of_nonneg_left hz (zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) i)).trans hscale
  have h := Entropy.abs_dyadicEntropy_sub_le_of_coupling
    (S.wordCoupling ν n) Prod.fst Prod.snd measurable_fst measurable_snd hX hY i K hdisp
  simpa only [hfst, hsnd] using h

end ExactOverlaps.SelfSimilar.System
