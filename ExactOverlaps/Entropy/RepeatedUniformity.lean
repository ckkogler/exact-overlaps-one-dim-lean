/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.Entropy.RawTupleUniformity
public import ExactOverlaps.Entropy.RepeatedComponentUniformity

/-!
# Repeated-convolution uniformity from mean component variance

This proves Hochman's Proposition 4.3 for arbitrary bounded Borel laws and
all integer coarse levels. The exceptional tuple weight is controlled by the
actual iid component-variance sampling law, and the remaining tuples satisfy
the proved Gaussian uniformity theorem. No tuple-uniformity premise remains.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace ExactOverlaps.Entropy

theorem exists_repeated_convolution_component_uniformity {σ δ : ℝ}
    (hσ : 0 < σ) (hδ : 0 < δ) {m : ℕ} (hm : 0 < m) :
    ∃ p K : ℕ, 0 < K ∧ ∀ n : ℕ, K ≤ n →
      ∀ (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ) (i : ℤ),
      σ < averageComponentVariance μ hμ i →
      componentEntropyLowerTailMass (realConvolutionPower μ n)
        (realConvolutionPower_hasBoundedSupport μ hμ n)
        (i - dyadicSqrtScale n + p) m δ < δ := by
  have hs : 0 < σ / 2 := by positivity
  have hd : 0 < δ ^ 2 / 4 := by positivity
  obtain ⟨p, K, hK, hp⟩ := exists_rawTuple_component_uniformity hs hd hm
  obtain ⟨L, hL⟩ := exists_nat_gt (16 / (σ ^ 2 * δ ^ 2))
  refine ⟨p, max K L, lt_of_lt_of_le hK (le_max_left _ _), ?_⟩
  intro n hn μ hμ i hmean
  have hnK : K ≤ n := (le_max_left _ _).trans hn
  have hnL : L ≤ n := (le_max_right _ _).trans hn
  have hnpos : 0 < n := lt_of_lt_of_le hK hnK
  have hsize : 16 < (n : ℝ) * σ ^ 2 * δ ^ 2 := by
    have hden : 0 < σ ^ 2 * δ ^ 2 := by positivity
    have hlt : 16 / (σ ^ 2 * δ ^ 2) < (n : ℝ) :=
      hL.trans_le (by exact_mod_cast hnL)
    have h := (div_lt_iff₀ hden).1 hlt
    nlinarith
  apply convolutionPower_uniformity_of_tuple_uniformity μ hμ i
    (i - dyadicSqrtScale n + p) hnpos hm hσ hδ hmean hsize
  intro w hw
  exact (hp n hnK μ i w (by nlinarith [hw])).le

end ExactOverlaps.Entropy
