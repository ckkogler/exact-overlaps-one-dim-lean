module

public import ExactOverlaps.VarianceEnergy.Normalization
import Mathlib.Data.Finset.Max

/-!
# Vanishing below the atom spacing

A sufficiently short half-open window contains at most one point of a fixed
finite support. Its unnormalized variance and the averaged local variance
therefore vanish. No lower bound on the masses of the atoms is required.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace ExactOverlaps.VarianceEnergy

lemma exists_pos_separation (s : Finset ℝ) :
    ∃ δ > 0, ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ |x - y| := by
  classical
  let distances := (s ×ˢ s).image (fun p : ℝ × ℝ ↦ if p.1 = p.2 then 1 else |p.1 - p.2|)
  let t := insert 1 distances
  have ht : t.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  refine ⟨t.min' ht, ?_, ?_⟩
  · have hd := Finset.min'_mem t ht
    rcases Finset.mem_insert.mp hd with hd | hd
    · rw [hd]
      norm_num
    · obtain ⟨⟨x, y⟩, _, heq⟩ := Finset.mem_image.mp hd
      rw [← heq]
      dsimp
      split_ifs with h
      · norm_num
      · exact abs_pos.mpr (sub_ne_zero.mpr h)
  · intro x hx y hy hxy
    apply Finset.min'_le
    apply Finset.mem_insert_of_mem
    apply Finset.mem_image.mpr
    exact ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, ite_eq_right hxy⟩

lemma localVarianceMass_eq_zero_of_ae (μ : Measure ℝ) (a r c : ℝ)
    (h : ∀ᵐ x ∂μ, x ∈ Ico a (a + r) → x = c) :
    localVarianceMass μ a r = 0 := by
  apply le_antisymm _ zero_le
  apply (localVarianceMass_le μ a r c).trans
  apply le_of_eq
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_of_ae h, ae_restrict_mem measurableSet_Ico] with x hx hmem
  simp [hx hmem]

lemma localVarianceMass_eq_zero_of_separation (μ : Measure ℝ) (s : Finset ℝ)
    (hμ : ∀ᵐ x ∂μ, x ∈ s) {δ r : ℝ}
    (hδ : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ |x - y|) (hr : r ≤ δ) (a : ℝ) :
    localVarianceMass μ a r = 0 := by
  classical
  by_cases hnonempty : ∃ c ∈ s, c ∈ Ico a (a + r)
  · obtain ⟨c, hcs, hc⟩ := hnonempty
    apply localVarianceMass_eq_zero_of_ae μ a r c
    filter_upwards [hμ] with x hx
    intro hxi
    by_contra hxc
    have hdist := hδ x hx c hcs hxc
    have hlt : |x - c| < r := by
      rw [abs_lt]
      constructor <;> linarith [hxi.1, hxi.2, hc.1, hc.2]
    linarith
  · apply localVarianceMass_eq_zero_of_ae μ a r 0
    filter_upwards [hμ] with x hx
    intro hxi
    exact (hnonempty ⟨x, hx, hxi⟩).elim

lemma normalizedLocalVariance_eq_zero_of_separation (μ : Measure ℝ) (s : Finset ℝ)
    (hμ : ∀ᵐ x ∂μ, x ∈ s) {δ r : ℝ}
    (hδ : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ |x - y|) (hr : r ≤ δ) :
    normalizedLocalVariance μ r = 0 := by
  simp [normalizedLocalVariance, localVarianceMass_eq_zero_of_separation μ s hμ hδ hr]

lemma exists_pos_vanishing_scale (μ : Measure ℝ) (s : Finset ℝ)
    (hμ : ∀ᵐ x ∂μ, x ∈ s) :
    ∃ δ > 0, ∀ r ≤ δ, normalizedLocalVariance μ r = 0 := by
  obtain ⟨δ, hδ, hsep⟩ := exists_pos_separation s
  exact ⟨δ, hδ, fun _ hr ↦ normalizedLocalVariance_eq_zero_of_separation μ s hμ hsep hr⟩

lemma exists_support_interval (μ : Measure ℝ) (s : Finset ℝ)
    (hμ : ∀ᵐ x ∂μ, x ∈ s) :
    ∃ b D : ℝ, ∀ᵐ x ∂μ, x ∈ Icc b (b + D) := by
  classical
  let t := insert 0 s
  have ht : t.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  refine ⟨t.min' ht, t.max' ht - t.min' ht, ?_⟩
  filter_upwards [hμ] with x hx
  have hxt : x ∈ t := Finset.mem_insert_of_mem hx
  constructor
  · exact Finset.min'_le _ _ hxt
  · simpa using Finset.le_max' _ _ hxt

end ExactOverlaps.VarianceEnergy
