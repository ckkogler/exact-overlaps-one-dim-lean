module

public import ExactOverlaps.SelfSimilar.StationaryApproximation
public import ExactOverlaps.SelfSimilar.SimilarityLaws
public import ExactOverlaps.Entropy.ConditionalConcavity

/-!
Conditioning finite words on their actual signed contraction ratio.
Only positive-mass ratio classes are used. Their conditional translation
laws reconstruct the original translation law with the genuine class masses.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal Classical BigOperators

namespace ExactOverlaps.SelfSimilar.System

open Entropy
variable {ι : Type*} [Fintype ι]

theorem wordRatioLaw_support_ne_zero (S : System ι) (n : ℕ)
    (r : (S.wordRatioLaw n).support) : (r : ℝ) ≠ 0 := by
  obtain ⟨w, _, hw⟩ := (PMF.mem_support_map_iff _ _ _).mp r.property
  rw [← hw]
  exact S.wordRatio_ne_zero n w

/-- The actual word law conditional on a signed ratio of positive mass. -/
noncomputable def ratioWordLaw (S : System ι) (n : ℕ)
    (r : (S.wordRatioLaw n).support) : PMF (Word ι n) :=
  conditionalPMF (S.wordLaw n) (S.wordRatio n)
    ⟨r, by simpa only [wordRatioLaw] using r.property⟩

theorem ratioWordLaw_support_ratio (S : System ι) (n : ℕ)
    (r : (S.wordRatioLaw n).support) (w : Word ι n)
    (hw : w ∈ (S.ratioWordLaw n r).support) : S.wordRatio n w = r := by
  rw [ratioWordLaw, conditionalPMF_support] at hw
  exact hw.1

noncomputable def ratioTranslationLaw (S : System ι) (n : ℕ)
    (r : (S.wordRatioLaw n).support) : PMF ℝ :=
  (S.ratioWordLaw n r).map (S.wordTranslation n)

theorem ratioTranslationLaw_support_finite (S : System ι) (n : ℕ)
    (r : (S.wordRatioLaw n).support) : (S.ratioTranslationLaw n r).support.Finite := by
  rw [ratioTranslationLaw, PMF.support_map]
  exact (Set.toFinite _).image _

noncomputable def ratioTranslationProbability (S : System ι) (n : ℕ)
    (r : (S.wordRatioLaw n).support) : ProbabilityMeasure ℝ :=
  (S.ratioTranslationLaw n r).toMeasure.toProbabilityMeasure

theorem ratioTranslationProbability_hasBoundedSupport (S : System ι) (n : ℕ)
    (r : (S.wordRatioLaw n).support) : HasBoundedSupport (S.ratioTranslationProbability n r) := by
  obtain ⟨B, _, hB⟩ := S.exists_uniform_translation_bound
  refine ⟨-B, B, ?_⟩
  change Icc (-B) B ∈ ae (S.ratioTranslationLaw n r).toMeasure
  rw [mem_ae_iff_prob_eq_one measurableSet_Icc]
  apply (PMF.toMeasure_apply_eq_one_iff _ measurableSet_Icc).mpr
  intro b hb
  obtain ⟨w, hw, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hb
  have hw' : w ∈ (S.wordLaw n).support := by
    rw [ratioWordLaw, conditionalPMF_support] at hw
    exact hw.2
  have htrans : S.wordTranslation n w ∈ (S.wordTranslationLaw n).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨w, hw', rfl⟩
  exact abs_le.mp (hB n _ htrans)

theorem wordTranslationLaw_eq_ratio_mixture (S : System ι) (n : ℕ) :
    S.wordTranslationLaw n = (supportLaw (S.wordRatioLaw n)).bind (S.ratioTranslationLaw n) := by
  change (S.wordLaw n).map (S.wordTranslation n) =
    (supportLaw ((S.wordLaw n).map (S.wordRatio n))).bind
      (fun r ↦ (conditionalPMF (S.wordLaw n) (S.wordRatio n) r).map (S.wordTranslation n))
  rw [← PMF.map_bind, bind_conditionalPMF (S.wordLaw n) (Set.toFinite _) (S.wordRatio n)]

theorem wordTranslationProbability_eq_ratio_mixture (S : System ι) (n : ℕ) :
    (S.wordTranslationProbability n : Measure ℝ) =
      (letI : Fintype (S.wordRatioLaw n).support := (S.wordRatioLaw_support_finite n).fintype
      ∑ r : (S.wordRatioLaw n).support, S.wordRatioLaw n r •
        (S.ratioTranslationProbability n r : Measure ℝ)) := by
  let : Fintype (S.wordRatioLaw n).support := (S.wordRatioLaw_support_finite n).fintype
  apply Measure.ext
  intro E hE
  change (S.wordTranslationLaw n).toMeasure E = _
  rw [S.wordTranslationLaw_eq_ratio_mixture n, PMF.toMeasure_bind_apply _ _ E hE, tsum_fintype]
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul, supportLaw_apply]
  rfl

/-- Dilation by the signed ratio; reflection is retained when the ratio is negative. -/
noncomputable def ratioDilation (S : System ι) (n : ℕ)
    (r : (S.wordRatioLaw n).support) : RealSimilarity :=
  ⟨r, S.wordRatioLaw_support_ne_zero n r, 0⟩

noncomputable def ratioScaledProbability (S : System ι) (μ : ProbabilityMeasure ℝ)
    (n : ℕ) (r : (S.wordRatioLaw n).support) : ProbabilityMeasure ℝ :=
  μ.map (S.ratioDilation n r)

theorem ratioScaledProbability_hasBoundedSupport (S : System ι) (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (n : ℕ) (r : (S.wordRatioLaw n).support) :
    HasBoundedSupport (S.ratioScaledProbability μ n r) :=
  (S.ratioDilation n r).hasBoundedSupport_map μ hμ

end ExactOverlaps.SelfSimilar.System
