/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.ConvolutionDisintegration.FactorSpace
public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# The canonical convolution-disintegration functional

An admissible family has a positive finite number of factors, each carried
by an interval of the indicated width. A disintegration is an actual
probability mixture of these convolutions. The functional is the infimum of
the genuine averaged exponential variance costs. Arbitrary source mixing
spaces are related to this canonical representation separately.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace ExactOverlaps.ConvolutionDisintegration

def HasIntervalWidth (μ : ProbabilityMeasure ℝ) (r : ℝ) : Prop :=
  ∃ a : ℝ, ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc a (a + r)

def Admissible (r : ℝ) (c : FactorFamily) : Prop :=
  ∀ j : Fin (c.1 + 1), HasIntervalWidth (Entropy.tupleCoordinate (c.1 + 1) c.2 j) r

def convolutionKernel : Kernel FactorFamily ℝ where
  toFun c := convolutionLaw c
  measurable' := measurable_subtype_coe.comp measurable_convolutionLaw

instance : IsMarkovKernel convolutionKernel where
  isProbabilityMeasure c := inferInstanceAs (IsProbabilityMeasure (convolutionLaw c : Measure ℝ))

def mixture (θ : ProbabilityMeasure FactorFamily) : ProbabilityMeasure ℝ :=
  ⟨convolutionKernel ∘ₘ (θ : Measure FactorFamily), inferInstance⟩

def IsDisintegration (μ : ProbabilityMeasure ℝ) (r : ℝ)
    (θ : ProbabilityMeasure FactorFamily) : Prop :=
  mixture θ = μ ∧ ∀ᵐ c ∂(θ : Measure FactorFamily), Admissible r c

def averageCost (r : ℝ) (θ : ProbabilityMeasure FactorFamily) : ℝ :=
  ∫ c, cost r c ∂(θ : Measure FactorFamily)

def costValues (μ : ProbabilityMeasure ℝ) (r : ℝ) : Set ℝ :=
  {v | ∃ θ : ProbabilityMeasure FactorFamily, IsDisintegration μ r θ ∧ v = averageCost r θ}

def W (μ : ProbabilityMeasure ℝ) (r : ℝ) : ℝ := sInf (costValues μ r)

lemma integrable_cost (r : ℝ) (θ : ProbabilityMeasure FactorFamily) :
    Integrable (cost r) (θ : Measure FactorFamily) := by
  apply memLp_one_iff_integrable.mp
  exact MemLp.of_bound (measurable_cost r).aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun c ↦ by
      rw [Real.norm_eq_abs, abs_of_pos (cost_pos r c)]
      exact cost_le_one r c))

lemma averageCost_nonneg (r : ℝ) (θ : ProbabilityMeasure FactorFamily) :
    0 ≤ averageCost r θ := integral_nonneg (fun c ↦ (cost_pos r c).le)

lemma averageCost_le_one (r : ℝ) (θ : ProbabilityMeasure FactorFamily) :
    averageCost r θ ≤ 1 := by
  have h := integral_mono (integrable_cost r θ) (integrable_const (1 : ℝ)) (cost_le_one r)
  have hθ : (θ : Measure FactorFamily).real univ = 1 := by simp
  change (∫ c, cost r c ∂(θ : Measure FactorFamily)) ≤ 1
  simpa only [integral_const, hθ, one_smul] using h

lemma costValues_bddBelow (μ : ProbabilityMeasure ℝ) (r : ℝ) : BddBelow (costValues μ r) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨θ, _, rfl⟩
  exact averageCost_nonneg r θ

lemma W_le_averageCost {μ : ProbabilityMeasure ℝ} {r : ℝ}
    {θ : ProbabilityMeasure FactorFamily} (hθ : IsDisintegration μ r θ) :
    W μ r ≤ averageCost r θ := csInf_le (costValues_bddBelow μ r) ⟨θ, hθ, rfl⟩

end ExactOverlaps.ConvolutionDisintegration
