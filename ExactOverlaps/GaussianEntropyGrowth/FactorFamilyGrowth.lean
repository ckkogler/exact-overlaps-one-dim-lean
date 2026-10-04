/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.GaussianEntropyGrowth.LawEntropyGrowth
public import ExactOverlaps.ConvolutionDisintegration.Admissibility

/-!
# Entropy growth for admissible convolution families

The finite-law theorem applies to the actual coordinates of every
admissible factor family. The output uses bounded-law scale entropy with
its support witness proved from the genuine factor intervals.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace ExactOverlaps.GaussianEntropyGrowth

open Entropy ConvolutionDisintegration

lemma tupleSum_eq_coordinate_sum {α : Type*} (f : α → ℝ) :
    ∀ n (w : FiniteTuple α n), tupleSum f n w = ∑ i : Fin n, f (tupleCoordinate n w i) := by
  intro n
  induction n with
  | zero => intro w; simp [tupleSum]
  | succ n ih =>
    intro w
    rw [tupleSum, Fin.sum_univ_succ]
    simp only [tupleCoordinate, Fin.cases_zero, Fin.cases_succ]
    rw [ih w.2]

lemma totalVariance_eq_coordinate_sum (c : FactorFamily) :
    totalVariance c = ∑ i : Fin (c.1 + 1),
      variance (id : ℝ → ℝ)
        ((tupleCoordinate (c.1 + 1) c.2 i : ProbabilityMeasure ℝ) : Measure ℝ) :=
  tupleSum_eq_coordinate_sum _ _ _

lemma admissible_convolution_hasBoundedSupport {s : ℝ} {c : FactorFamily}
    (hc : Admissible s c) : HasBoundedSupport (convolutionLaw c) := by
  rw [convolutionLaw, tupleConvolution_eq_continuousSumLaw]
  apply continuousSumLaw_hasBoundedSupport
  intro i
  obtain ⟨a, ha⟩ := hc i
  exact ⟨a, a + s, ha⟩

theorem admissible_factor_entropy_growth (C : ℕ) (hC : 1 < C) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∃ A > 0, ∀ (r : ℝ) (hr : 0 < r) (c : FactorFamily)
      (hc : Admissible (δ * r) c), A * r ^ 2 ≤ totalVariance c →
      Real.log (C : ℝ) - ε < ScaleEntropy.entropyBetween (convolutionLaw c)
        (admissible_convolution_hasBoundedSupport hc) r hr ((C : ℝ) * r)
        (mul_pos (by exact_mod_cast (lt_trans Nat.zero_lt_one hC)) hr) := by
  obtain ⟨δ, hδ, A, hA, hgrowth⟩ := bounded_law_entropy_growth.{0} C hC hε
  refine ⟨δ, hδ, A, hA, ?_⟩
  intro r hr c hc hvariance
  let ν := fun i : Fin (c.1 + 1) ↦ tupleCoordinate (c.1 + 1) c.2 i
  have hwidth (i : Fin (c.1 + 1)) :
      ∃ a b : ℝ, b - a ≤ δ * r ∧ ∀ᵐ x ∂(ν i : Measure ℝ), x ∈ Icc a b := by
    obtain ⟨a, ha⟩ := hc i
    exact ⟨a, a + δ * r, by linarith, ha⟩
  have hvar : A * r ^ 2 ≤ ∑ i, variance (id : ℝ → ℝ) (ν i : Measure ℝ) := by
    simpa only [totalVariance_eq_coordinate_sum] using hvariance
  have h := hgrowth r hr ν hwidth hvar
  have he : convolutionLaw c = continuousSumLaw ν :=
    tupleConvolution_eq_continuousSumLaw id (c.1 + 1) c.2
  rw [← he, GaussianScaleEntropy.entropyBetween_eq_bounded (convolutionLaw c)
    (admissible_convolution_hasBoundedSupport hc) hr
    (mul_pos (by exact_mod_cast (lt_trans Nat.zero_lt_one hC)) hr)] at h
  exact h

end ExactOverlaps.GaussianEntropyGrowth
