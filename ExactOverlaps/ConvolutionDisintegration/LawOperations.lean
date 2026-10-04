/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.Entropy.RealConvolution
public import Mathlib.Probability.Kernel.MeasurableIntegral
public import Mathlib.Probability.Moments.Variance

/-!
# Measurable operations on real probability laws

The canonical convolution-disintegration space uses the actual Giry measurable
space of probability measures. Means, variances, Dirac laws and convolution
are measurable operations on these laws, rather than assumed structure fields.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory

namespace ExactOverlaps.ConvolutionDisintegration

def lawKernel : Kernel (ProbabilityMeasure ℝ) ℝ where
  toFun μ := μ
  measurable' := measurable_subtype_coe

instance : IsMarkovKernel lawKernel where
  isProbabilityMeasure μ := inferInstanceAs (IsProbabilityMeasure (μ : Measure ℝ))

lemma measurable_mean :
    Measurable (fun μ : ProbabilityMeasure ℝ ↦ ∫ x : ℝ, x ∂(μ : Measure ℝ)) :=
  (measurable_id.stronglyMeasurable.integral_kernel (κ := lawKernel)).measurable

lemma measurable_variance :
    Measurable (fun μ : ProbabilityMeasure ℝ ↦ variance (id : ℝ → ℝ) (μ : Measure ℝ)) := by
  have hf : Measurable (fun p : ProbabilityMeasure ℝ × ℝ ↦
      (p.2 - ∫ x : ℝ, x ∂(p.1 : Measure ℝ)) ^ 2) :=
    (measurable_snd.sub (measurable_mean.comp measurable_fst)).pow_const 2
  have h := hf.stronglyMeasurable.integral_kernel_prod_right' (κ := lawKernel)
  have hm := h.measurable
  change Measurable (fun μ : ProbabilityMeasure ℝ ↦
    ∫ x : ℝ, (x - ∫ t : ℝ, t ∂(μ : Measure ℝ)) ^ 2 ∂(μ : Measure ℝ)) at hm
  simpa only [variance_eq_integral measurable_id.aemeasurable, id_eq] using hm

lemma measurable_dirac_law :
    Measurable (fun x : ℝ ↦ (⟨Measure.dirac x, inferInstance⟩ : ProbabilityMeasure ℝ)) :=
  Measure.measurable_dirac.subtype_mk

lemma measurable_convolution :
    Measurable (fun p : ProbabilityMeasure ℝ × ProbabilityMeasure ℝ ↦
      Entropy.realConvolution p.1 p.2) := by
  apply Measurable.subtype_mk
  exact (Measure.measurable_map (fun x : ℝ × ℝ ↦ x.1 + x.2)
    (measurable_fst.add measurable_snd)).comp ProbabilityMeasure.measurable_fun_prod

end ExactOverlaps.ConvolutionDisintegration
