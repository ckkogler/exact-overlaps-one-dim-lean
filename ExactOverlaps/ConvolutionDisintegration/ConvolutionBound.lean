/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.ConvolutionDisintegration.Concatenation
public import ExactOverlaps.ConvolutionDisintegration.Convexity
public import Mathlib.Probability.Kernel.Composition.Lemmas
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Submultiplicativity under actual convolution

Take the independent product of two mixing laws and concatenate the factor
families. The resulting mixture is the actual convolution, and its average
cost is the product of the original costs. Approximation of both infima
then gives the convolution inequality for W.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace ExactOverlaps.ConvolutionDisintegration

def productMix (θ φ : ProbabilityMeasure FactorFamily) :
    ProbabilityMeasure (FactorFamily × FactorFamily) :=
  ⟨(θ : Measure FactorFamily).prod (φ : Measure FactorFamily), inferInstance⟩

lemma familyKernel_concatenate :
    familyKernel (fun p : FactorFamily × FactorFamily ↦ concatenate p.1 p.2)
      measurable_concatenate =
      (convolutionKernel ∥ₖ convolutionKernel).map (fun z : ℝ × ℝ ↦ z.1 + z.2) := by
  ext1 p
  change (convolutionLaw (concatenate p.1 p.2) : Measure ℝ) = _
  have hm : Measurable (fun z : ℝ × ℝ ↦ z.1 + z.2) := measurable_fst.add measurable_snd
  rw [convolutionLaw_concatenate, Kernel.map_apply _ hm,
    Kernel.parallelComp_apply]
  rfl

lemma familyMixture_concatenate (θ φ : ProbabilityMeasure FactorFamily) :
    familyMixture (productMix θ φ) (fun p ↦ concatenate p.1 p.2) measurable_concatenate =
      Entropy.realConvolution (mixture θ) (mixture φ) := by
  apply Subtype.ext
  have hm : Measurable (fun z : ℝ × ℝ ↦ z.1 + z.2) := measurable_fst.add measurable_snd
  change (familyKernel (fun p ↦ concatenate p.1 p.2) measurable_concatenate) ∘ₘ
      ((θ : Measure FactorFamily).prod (φ : Measure FactorFamily)) =
    ((convolutionKernel ∘ₘ (θ : Measure FactorFamily)).prod
      (convolutionKernel ∘ₘ (φ : Measure FactorFamily))).map (fun z : ℝ × ℝ ↦ z.1 + z.2)
  rw [Measure.prod_comp_left, Measure.prod_comp_right, Measure.comp_assoc,
    Kernel.parallelComp_comp_parallelComp, Kernel.comp_id, Kernel.id_comp,
    Measure.map_comp _ _ hm, familyKernel_concatenate]

def convolutionDisintegration (θ φ : ProbabilityMeasure FactorFamily) :
    ProbabilityMeasure FactorFamily := (productMix θ φ).map (fun p ↦ concatenate p.1 p.2)

lemma isDisintegration_convolution {μ ν : ProbabilityMeasure ℝ} {r : ℝ}
    {θ φ : ProbabilityMeasure FactorFamily} (hθ : IsDisintegration μ r θ)
    (hφ : IsDisintegration ν r φ) :
    IsDisintegration (Entropy.realConvolution μ ν) r (convolutionDisintegration θ φ) := by
  apply (isDisintegration_map_iff _ r (productMix θ φ) _ measurable_concatenate).mpr
  constructor
  · rw [familyMixture_concatenate, hθ.1, hφ.1]
  · change ∀ᵐ p ∂((θ : Measure FactorFamily).prod (φ : Measure FactorFamily)),
      Admissible r (concatenate p.1 p.2)
    apply (Measure.ae_prod_iff_ae_ae (measurable_concatenate (measurableSet_admissible r))).mpr
    filter_upwards [hθ.2] with c hc
    exact hφ.2.mono (fun _ hd ↦ admissible_concatenate hc hd)

lemma averageCost_convolution (θ φ : ProbabilityMeasure FactorFamily) (r : ℝ) :
    averageCost r (convolutionDisintegration θ φ) = averageCost r θ * averageCost r φ := by
  rw [convolutionDisintegration, averageCost_map_eq _ _ measurable_concatenate r]
  simp only [cost_concatenate]
  exact integral_prod_mul (cost r) (cost r)

theorem W_convolution_le {r : ℝ} (hr : 0 ≤ r) (μ ν : ProbabilityMeasure ℝ) :
    W (Entropy.realConvolution μ ν) r ≤ W μ r * W ν r := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have he : 0 < ε / 2 := by positivity
  obtain ⟨θ, hθ, hcθ⟩ := exists_cost_lt hr μ he
  obtain ⟨φ, hφ, hcφ⟩ := exists_cost_lt hr ν he
  have h := W_le_averageCost (isDisintegration_convolution hθ hφ)
  rw [averageCost_convolution] at h
  have hA := mul_le_mul_of_nonneg_left hcφ.le (averageCost_nonneg r θ)
  have hB := mul_le_mul_of_nonneg_right hcθ.le (W_nonneg hr ν)
  have hC := mul_le_mul_of_nonneg_right (averageCost_le_one r θ) he.le
  have hD := mul_le_mul_of_nonneg_right (W_le_one hr ν) he.le
  nlinarith

end ExactOverlaps.ConvolutionDisintegration
