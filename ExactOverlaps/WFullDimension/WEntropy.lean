/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.WFullDimension.CostThreshold
public import ExactOverlaps.WFullDimension.MixtureEntropy
public import ExactOverlaps.WFullDimension.EntropyBounds
public import ExactOverlaps.ConvolutionDisintegration.PointwiseReplacement
public import ExactOverlaps.GaussianEntropyGrowth.FactorFamilyGrowth

/-!
Small convolution-disintegration cost forces a lower entropy bound. The
infimum is approximated by an actual disintegration, repaired on a null set
to be admissible everywhere, and integrated using proved kernel concavity.
-/

@[expose] public section

noncomputable section
open MeasureTheory

namespace ExactOverlaps.WFullDimension

open ConvolutionDisintegration Entropy ScaleEntropy GaussianEntropyGrowth

theorem entropy_lower_bound_of_W_lt {δ A L : ℝ}
    (hδ : 0 < δ) (hL : 0 ≤ L)
    (hgrowth : ∀ (r : ℝ) (hr : 0 < r) (c : FactorFamily)
      (hc : Admissible (δ * r) c), A * r ^ 2 ≤ totalVariance c →
        L ≤ entropyBetween (convolutionLaw c)
          (admissible_convolution_hasBoundedSupport hc) r hr (2 * r) (by positivity))
    (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ)
    (r : ℝ) (hr : 0 < r) {b : ℝ} (hW : W μ (δ * r) < b) :
    L * (1 - Real.exp (4 * A / δ ^ 2) * b) ≤
      entropyBetween μ hμ r hr (2 * r) (by positivity) := by
  obtain ⟨v, hv, hvb⟩ := exists_lt_of_csInf_lt
    (costValues_nonempty (mul_pos hδ hr).le μ) hW
  obtain ⟨θ, hθ, rfl⟩ := hv
  obtain ⟨f, hf, hadm, hmix, hcost⟩ :=
    pointwise_canonical_representation (mul_pos hδ hr).le θ hθ
  have hF (c : FactorFamily) : HasBoundedSupport (convolutionLaw (f c)) :=
    admissible_convolution_hasBoundedSupport (hadm c)
  have hμ' : HasBoundedSupport (familyMixture θ f hf) := by rwa [hmix]
  have hbound (c : FactorFamily) :
      L * (1 - Real.exp (4 * A / δ ^ 2) * cost (δ * r) (f c)) ≤
        entropyBetween (convolutionLaw (f c)) (hF c) r hr (2 * r) (by positivity) := by
    apply entropy_lower_bound_from_cost hδ hr hL
      (entropyBetween_double_bounds (convolutionLaw (f c)) (hF c) r hr).1
    exact hgrowth r hr (f c) (hadm c)
  have hh := family_entropy_lower_bound θ f hf hF hμ' r hr (δ * r) L
    (Real.exp (4 * A / δ ^ 2)) hbound
  rw [hcost] at hh
  have hh' : L * (1 - Real.exp (4 * A / δ ^ 2) * averageCost (δ * r) θ) ≤
      entropyBetween μ hμ r hr (2 * r) (by positivity) := by
    simpa only [hmix] using hh
  apply le_trans _ hh'
  have hK : 0 ≤ Real.exp (4 * A / δ ^ 2) := Real.exp_nonneg _
  have h := mul_le_mul_of_nonneg_left hvb.le hK
  exact mul_le_mul_of_nonneg_left (sub_le_sub_left h 1) hL

end ExactOverlaps.WFullDimension
