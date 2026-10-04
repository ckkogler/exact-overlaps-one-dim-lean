module

public import ExactOverlaps.VarianceEnergy.FiniteEnergy
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# The tail estimate in terms of support diameter

For a finite support, the leftmost point gives an enclosing interval with
length bounded by the diameter. This connects the interval version of the
tail bound to the source statement's diameter hypothesis.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace ExactOverlaps.VarianceEnergy

lemma exists_interval_of_pairwise_distance (s : Finset ℝ) {D : ℝ}
    (hD : ∀ x ∈ s, ∀ y ∈ s, |x - y| ≤ D) :
    ∃ b : ℝ, ∀ x ∈ s, x ∈ Icc b (b + D) := by
  classical
  by_cases hs : s.Nonempty
  · refine ⟨s.min' hs, ?_⟩
    intro x hx
    refine ⟨Finset.min'_le s x hx, ?_⟩
    have h := hD x hx (s.min' hs) (Finset.min'_mem s hs)
    linarith [le_abs_self (x - s.min' hs)]
  · refine ⟨0, ?_⟩
    intro x hx
    exact (hs ⟨x, hx⟩).elim

lemma energy_tail_le_of_pairwise_distance (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (s : Finset ℝ) (hs : ∀ᵐ x ∂μ, x ∈ s) {D R : ℝ}
    (hD : ∀ x ∈ s, ∀ y ∈ s, |x - y| ≤ D) (hR : 0 < R) :
    (energy μ).toReal - (energyBelow μ R).toReal ≤ D ^ 2 / (2 * R ^ 2) := by
  obtain ⟨b, hb⟩ := exists_interval_of_pairwise_distance s hD
  apply energy_toReal_sub_energyBelow_le μ s hs (b := b) _ hR
  filter_upwards [hs] with x hx
  exact hb x hx

lemma energy_tail_le_of_diameter (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (s : Finset ℝ) (hs : ∀ᵐ x ∂μ, x ∈ s) {D R : ℝ}
    (hD : Metric.diam (s : Set ℝ) ≤ D) (hR : 0 < R) :
    (energy μ).toReal - (energyBelow μ R).toReal ≤ D ^ 2 / (2 * R ^ 2) := by
  apply energy_tail_le_of_pairwise_distance μ s hs _ hR
  intro x hx y hy
  have h := Metric.dist_le_diam_of_mem s.finite_toSet.isBounded hx hy
  have hxy : |x - y| ≤ Metric.diam (s : Set ℝ) := by simpa only [Real.dist_eq] using h
  exact hxy.trans hD

end ExactOverlaps.VarianceEnergy
