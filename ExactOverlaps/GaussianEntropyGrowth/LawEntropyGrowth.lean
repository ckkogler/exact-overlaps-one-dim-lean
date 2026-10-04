/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.GaussianEntropyGrowth.EntropyGrowth
public import ExactOverlaps.Entropy.ContinuousSumMoments

/-!
# Entropy growth for finite lists of bounded probability laws

The laws are realized on their genuine finite product measure. Their
coordinates are centered by their actual means, and translation invariance
returns the result for the original convolution. Support intervals may be
located anywhere and need only have the required uniform width.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

universe u

namespace ExactOverlaps.GaussianEntropyGrowth

open GaussianScaleEntropy Entropy

lemma centered_sumLaw_eq_translate {ι : Type*} [Fintype ι]
    (ν : ι → ProbabilityMeasure ℝ) :
    sumLaw (continuousProductLaw ν : Measure (ι → ℝ)) (centeredProductCoordinate ν) Finset.univ =
      translate (continuousSumLaw ν) (-(∑ i, realLawMean (ν i))) := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [sumLaw_toMeasure, translate, ProbabilityMeasure.toMeasure_map]
  have h := continuousSumLaw_map_center ν
  rw [ProbabilityMeasure.toMeasure_map] at h
  simpa only [sub_eq_add_neg] using h.symm

lemma variance_centeredProductCoordinate {ι : Type*} [Fintype ι]
    (ν : ι → ProbabilityMeasure ℝ) (hν : ∀ i, HasBoundedSupport (ν i)) (i : ι) :
    variance (centeredProductCoordinate ν i) (continuousProductLaw ν : Measure (ι → ℝ)) =
      variance (id : ℝ → ℝ) (ν i : Measure ℝ) := by
  rw [variance_eq_integral (centeredProductCoordinate_memLp ν hν 2 i).aemeasurable,
    integral_centeredProductCoordinate ν hν i]
  simpa only [sub_zero] using integral_sq_centeredProductCoordinate ν i

theorem bounded_law_entropy_growth (C : ℕ) (hC : 1 < C) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∃ A > 0,
      ∀ {ι : Type u} [Fintype ι] (r : ℝ), 0 < r →
      ∀ (ν : ι → ProbabilityMeasure ℝ),
      (∀ i, ∃ a b : ℝ, b - a ≤ δ * r ∧ ∀ᵐ x ∂(ν i : Measure ℝ), x ∈ Icc a b) →
      A * r ^ 2 ≤ ∑ i, variance (id : ℝ → ℝ) (ν i : Measure ℝ) →
      Real.log (C : ℝ) - ε < entropyBetween (continuousSumLaw ν) r ((C : ℝ) * r) := by
  obtain ⟨δ, hδ, A, hA, hgrowth⟩ := bounded_independent_sum_entropy_growth.{u, u} C hC hε
  refine ⟨δ, hδ, A, hA, ?_⟩
  intro ι _ r hr ν hwidth hvariance
  choose a b hlen hab using hwidth
  have hν (i : ι) : HasBoundedSupport (ν i) := ⟨a i, b i, hab i⟩
  have hR (i : ι) : ∀ᵐ w ∂(continuousProductLaw ν : Measure (ι → ℝ)),
      |centeredProductCoordinate ν i w| ≤ δ * r :=
    (abs_centeredProductCoordinate_le ν i (hab i)).mono (fun _ hw ↦ hw.trans (hlen i))
  have hvar : A * r ^ 2 ≤ ∑ i, variance (centeredProductCoordinate ν i)
      (continuousProductLaw ν : Measure (ι → ℝ)) := by
    simpa only [variance_centeredProductCoordinate ν hν] using hvariance
  have h := hgrowth (continuousProductLaw ν : Measure (ι → ℝ)) r hr
    (centeredProductCoordinate ν)
    (fun i ↦ (centeredProductCoordinate_memLp ν hν 2 i).aemeasurable)
    (centeredProductCoordinate_independent ν) (integral_centeredProductCoordinate ν hν) hR hvar
  rw [centered_sumLaw_eq_translate,
    entropyBetween_translate (continuousSumLaw ν) (continuousSumLaw_hasBoundedSupport ν hν)
      _ hr (mul_pos (by exact_mod_cast (lt_trans Nat.zero_lt_one hC)) hr)] at h
  exact h

end ExactOverlaps.GaussianEntropyGrowth
