module

public import ExactOverlaps.SelfSimilar.FiniteAffineMixture
public import ExactOverlaps.SelfSimilar.Similarity
public import ExactOverlaps.StoppedConcatenation.DiscreteWJensen
public import ExactOverlaps.ConvolutionDisintegration.ConvolutionBound

/-!
Adding an independent tail to a finite affine mixture does not increase
the average W of the translations conditioned on their signed ratios.
The ratio-conditioned convolutions are actual probability laws.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal Classical

namespace ExactOverlaps.MainTheorem

open Entropy ConvolutionDisintegration SelfSimilar FiniteProbability

variable {α β : Type*} [Fintype α]

theorem finiteMix_eq_conditional_mixture (p : PMF α) (f : α → β)
    (μ : α → ProbabilityMeasure ℝ) :
    finiteMix p μ =
      (letI := (show (p.map f).support.Finite from by
        simpa only [PMF.support_map] using (Set.toFinite p.support).image f).fintype
      finiteMix (supportLaw (p.map f)) (fun b ↦ finiteMix (conditionalPMF p f b) μ)) := by
  let hf : (p.map f).support.Finite := by simpa only [PMF.support_map] using (Set.toFinite p.support).image f
  let := hf.fintype
  have hw (a : α) : ∑ b : (p.map f).support, (p.map f) b * conditionalPMF p f b a = p a := by
    have h := congrArg (fun q : PMF α ↦ q a) (bind_conditionalPMF p (Set.toFinite _) f)
    simpa only [PMF.bind_apply, tsum_fintype, supportLaw_apply] using h
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext
  intro E hE
  change (∑ a, p a • (μ a : Measure ℝ)) E =
    (∑ b : (p.map f).support, (supportLaw (p.map f)) b •
      (∑ a, conditionalPMF p f b a • (μ a : Measure ℝ))) E
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    supportLaw_apply, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_mul, hw]

noncomputable def ratioTailLaw (p : PMF α) (g : α → RealSimilarity)
    (μ : ProbabilityMeasure ℝ) (b : (p.map (fun a ↦ (g a).ratio)).support) :
    ProbabilityMeasure ℝ :=
  realConvolution (pmfLaw ((conditionalPMF p (fun a ↦ (g a).ratio) b).map (fun a ↦ (g a).shift)))
    (μ.map (fun x ↦ (b : ℝ) * x))

theorem ratioTailLaw_eq_finiteMix (p : PMF α) (g : α → RealSimilarity)
    (μ : ProbabilityMeasure ℝ) (b : (p.map (fun a ↦ (g a).ratio)).support) :
    ratioTailLaw p g μ b = finiteMix (conditionalPMF p (fun a ↦ (g a).ratio) b)
      (fun a ↦ μ.map (g a)) := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [ratioTailLaw, realConvolution_toMeasure]
  change ((conditionalPMF p (fun a ↦ (g a).ratio) b).map (fun a ↦ (g a).shift)).toMeasure ∗
    (μ : Measure ℝ).map (fun x ↦ (b : ℝ) * x) = _
  rw [finite_translation_convolution]
  change (∑ a, conditionalPMF p (fun a ↦ (g a).ratio) b a •
    (μ : Measure ℝ).map (fun x ↦ (b : ℝ) * x + (g a).shift)) =
    ∑ a, conditionalPMF p (fun a ↦ (g a).ratio) b a • (μ : Measure ℝ).map (g a)
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ (conditionalPMF p (fun a ↦ (g a).ratio) b).support
  · have he := (conditionalPMF_support p (fun a ↦ (g a).ratio) b ▸ ha).1
    congr 2
    funext x
    rw [he]
  · have hz : conditionalPMF p (fun a ↦ (g a).ratio) b a = 0 := by simpa using ha
    simp only [hz, zero_smul]

theorem W_finite_affine_tail_le (p : PMF α) (g : α → RealSimilarity)
    (μ : ProbabilityMeasure ℝ) {r : ℝ} (hr : 0 ≤ r) :
    W (finiteMix p (fun a ↦ μ.map (g a))) r ≤
      meanConditionalMapW p (Set.toFinite _) (fun a ↦ (g a).ratio) (fun a ↦ (g a).shift) r := by
  let f : α → ℝ := fun a ↦ (g a).ratio
  let hf : (p.map f).support.Finite := by simpa only [PMF.support_map] using (Set.toFinite p.support).image f
  let := hf.fintype
  have hm : finiteMix p (fun a ↦ μ.map (g a)) =
      finiteMix (supportLaw (p.map f)) (ratioTailLaw p g μ) := by
    rw [finiteMix_eq_conditional_mixture p f]
    congr 1
    funext b
    exact (ratioTailLaw_eq_finiteMix p g μ b).symm
  rw [hm]
  have h := W_finiteMix_le (supportLaw (p.map f)) (ratioTailLaw p g μ) hr
  rw [meanConditionalMapW, meanFiberFunctional_eq_sum]
  apply h.trans
  apply Finset.sum_le_sum
  intro b _
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  exact (W_convolution_le hr _ _).trans
    (mul_le_of_le_one_right (W_nonneg hr _) (W_le_one hr _))

end ExactOverlaps.MainTheorem
