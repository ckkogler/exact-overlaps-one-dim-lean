module

public import ExactOverlaps.SelfSimilar.RatioConditioning
public import ExactOverlaps.SelfSimilar.FiniteAffineMixture

/-!
The exact convolution decomposition after conditioning words on their signed
contraction ratio. The class weights and translation distributions are the
actual conditional probabilities of the original word law.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal Classical BigOperators

namespace ExactOverlaps.SelfSimilar.System

open Entropy
variable {ι : Type*} [Fintype ι]

theorem bind_ratioWordLaw (S : System ι) (n : ℕ) :
    (supportLaw (S.wordRatioLaw n)).bind (S.ratioWordLaw n) = S.wordLaw n := by
  change (supportLaw ((S.wordLaw n).map (S.wordRatio n))).bind
    (conditionalPMF (S.wordLaw n) (S.wordRatio n)) = _
  exact bind_conditionalPMF (S.wordLaw n) (Set.toFinite _) (S.wordRatio n)

/-- Each signed ratio class gives a genuine convolution, including reflected tails. -/
noncomputable def ratioConvolutionProbability (S : System ι) (μ : ProbabilityMeasure ℝ)
    (n : ℕ) (r : (S.wordRatioLaw n).support) : ProbabilityMeasure ℝ :=
  realConvolution (S.ratioTranslationProbability n r) (S.ratioScaledProbability μ n r)

theorem ratioConvolutionProbability_hasBoundedSupport (S : System ι)
    (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ) (n : ℕ)
    (r : (S.wordRatioLaw n).support) :
    HasBoundedSupport (S.ratioConvolutionProbability μ n r) :=
  realConvolution_hasBoundedSupport _ _ (S.ratioTranslationProbability_hasBoundedSupport n r)
    (S.ratioScaledProbability_hasBoundedSupport μ hμ n r)

theorem ratioConvolutionProbability_eq_word_mixture (S : System ι)
    (μ : ProbabilityMeasure ℝ) (n : ℕ) (r : (S.wordRatioLaw n).support) :
    (S.ratioConvolutionProbability μ n r : Measure ℝ) =
      ∑ w, S.ratioWordLaw n r w • (μ : Measure ℝ).map (S.wordMap n w) := by
  rw [ratioConvolutionProbability, realConvolution_toMeasure]
  change (PMF.map (S.wordTranslation n) (S.ratioWordLaw n r)).toMeasure ∗
    (μ : Measure ℝ).map (fun x ↦ (r : ℝ) * x + 0) = _
  simp only [add_zero]
  rw [finite_translation_convolution]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hw : w ∈ (S.ratioWordLaw n r).support
  · have hr := S.ratioWordLaw_support_ratio n r w hw
    congr 2
    funext x
    change (r : ℝ) * x + S.wordTranslation n w =
      S.wordRatio n w * x + S.wordTranslation n w
    rw [hr]
  · have hz : S.ratioWordLaw n r w = 0 := not_not.mp hw
    simp only [hz, zero_smul]

/-- Exact stationarity as a finite mixture of ratio-conditioned convolutions. -/
theorem stationary_eq_ratio_convolution_mixture (S : System ι)
    (μ : ProbabilityMeasure ℝ) (hμ : S.IsStationary (μ : Measure ℝ)) (n : ℕ) :
    (μ : Measure ℝ) =
      (letI : Fintype (S.wordRatioLaw n).support := (S.wordRatioLaw_support_finite n).fintype
      ∑ r : (S.wordRatioLaw n).support, S.wordRatioLaw n r •
        (S.ratioConvolutionProbability μ n r : Measure ℝ)) := by
  let : Fintype (S.wordRatioLaw n).support := (S.wordRatioLaw_support_finite n).fintype
  have hw (w : Word ι n) :
      ∑ r : (S.wordRatioLaw n).support, S.wordRatioLaw n r * S.ratioWordLaw n r w =
        S.wordWeight n w := by
    have h := congrArg (fun p : PMF (Word ι n) ↦ p w) (S.bind_ratioWordLaw n)
    simpa only [PMF.bind_apply, tsum_fintype, supportLaw_apply, wordLaw_apply] using h
  apply Measure.ext
  intro E hE
  rw [S.word_decomposition hμ n hE]
  simp only [S.ratioConvolutionProbability_eq_word_mixture μ n,
    Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (S.wordMap n _).measurable hE, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  rw [← Finset.sum_mul, hw]

end ExactOverlaps.SelfSimilar.System
