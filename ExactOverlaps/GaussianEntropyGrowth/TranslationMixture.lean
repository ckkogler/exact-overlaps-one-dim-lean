/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.GaussianEntropyGrowth.Translation
public import ExactOverlaps.ScaleEntropy.KernelConcavity
public import ExactOverlaps.Entropy.RealConvolution

/-!
# Convolution as the genuine mixture of translations

A Markov kernel sends the mixing parameter b to the actual translate of
the first probability law. Its mixture against a second law is exactly
their convolution, so scale-entropy concavity applies to independent sums.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace ExactOverlaps.GaussianEntropyGrowth

def translationKernel (μ : ProbabilityMeasure ℝ) : Kernel ℝ ℝ where
  toFun b := translate μ b
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro E hE
    have hm : MeasurableSet {p : ℝ × ℝ | p.2 + p.1 ∈ E} :=
      (measurable_snd.add measurable_fst) hE
    have h := measurable_measure_prodMk_left (ν := (μ : Measure ℝ)) hm
    convert h using 1
    funext b
    change ((μ : Measure ℝ).map (fun x ↦ x + b)) E = (μ : Measure ℝ) {x | x + b ∈ E}
    exact Measure.map_apply (measurable_id.add_const b) hE

instance (μ : ProbabilityMeasure ℝ) : IsMarkovKernel (translationKernel μ) where
  isProbabilityMeasure b := inferInstanceAs (IsProbabilityMeasure (translate μ b : Measure ℝ))

lemma componentLaw_translationKernel (μ : ProbabilityMeasure ℝ) (b : ℝ) :
    ScaleEntropy.componentLaw (translationKernel μ) b = translate μ b := rfl

lemma mixtureLaw_translationKernel (μ ν : ProbabilityMeasure ℝ) :
    ScaleEntropy.mixtureLaw (translationKernel μ) (ν : Measure ℝ) =
      Entropy.realConvolution μ ν := by
  rw [Entropy.realConvolution_comm μ ν]
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext
  intro E hE
  change (ν : Measure ℝ).bind (translationKernel μ) E =
    (((ν : Measure ℝ).prod (μ : Measure ℝ)).map (fun p : ℝ × ℝ ↦ p.1 + p.2)) E
  have hm : Measurable (fun p : ℝ × ℝ ↦ p.1 + p.2) := by fun_prop
  rw [Measure.bind_apply hE (translationKernel μ).aemeasurable,
    Measure.map_apply hm hE, Measure.prod_apply (hm hE)]
  apply lintegral_congr
  intro b
  change ((μ : Measure ℝ).map (fun x ↦ x + b)) E = _
  rw [Measure.map_apply (by fun_prop) hE]
  congr 1
  ext x
  simp only [Set.mem_preimage]
  rw [add_comm x b]

theorem entropyBetween_convolution_le (μ ν : ProbabilityMeasure ℝ)
    (hμ : Entropy.HasBoundedSupport μ) (hν : Entropy.HasBoundedSupport ν)
    {r : ℝ} (hr : 0 < r) (C : ℕ) (hC : 0 < C) :
    GaussianScaleEntropy.entropyBetween μ r ((C : ℝ) * r) ≤
      GaussianScaleEntropy.entropyBetween (Entropy.realConvolution μ ν) r ((C : ℝ) * r) := by
  have hκ (b : ℝ) : Entropy.HasBoundedSupport
      (ScaleEntropy.componentLaw (translationKernel μ) b) := translate_hasBoundedSupport μ hμ b
  have hm : Entropy.HasBoundedSupport
      (ScaleEntropy.mixtureLaw (translationKernel μ) (ν : Measure ℝ)) := by
    rw [mixtureLaw_translationKernel]
    exact Entropy.realConvolution_hasBoundedSupport μ ν hμ hν
  have hR : 0 < (C : ℝ) * r := mul_pos (Nat.cast_pos.mpr hC) hr
  have h := ScaleEntropy.entropyBetween_kernel_mixture_le (translationKernel μ)
    (ν : Measure ℝ) hκ hm r hr C hC
  have hνmass : (ν : Measure ℝ).real univ = 1 := by simp
  simp_rw [← GaussianScaleEntropy.entropyBetween_eq_bounded _ _ hr hR] at h
  simp only [componentLaw_translationKernel, entropyBetween_translate μ hμ _ hr hR,
    mixtureLaw_translationKernel, integral_const, hνmass, one_smul] at h
  exact h

end ExactOverlaps.GaussianEntropyGrowth
