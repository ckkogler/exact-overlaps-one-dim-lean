/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Tactic

/-!
# Finite translated-grid averaging

Averaging a finite sum over one grid period exactly recovers the integral
over the tiled interval. A strict average lower bound therefore supplies
one translated grid with the same lower bound on its sampled sum.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace ExactOverlaps.WImprovement

lemma intervalIntegrable_grid_translate {f : ℝ → ℝ} (hf : Integrable f)
    (a d : ℝ) (j : ℕ) :
    IntervalIntegrable (fun u ↦ f (a + u + (j : ℝ) * d)) volume 0 d := by
  have h : IntervalIntegrable f volume (a + (j : ℝ) * d) (d + (a + (j : ℝ) * d)) :=
    hf.intervalIntegrable
  have ht := h.comp_add_right (a + (j : ℝ) * d)
  rw [sub_self, add_sub_cancel_right] at ht
  simpa only [add_assoc, add_comm, add_left_comm] using ht

lemma integral_finite_grid {f : ℝ → ℝ} (hf : Integrable f) (a d : ℝ) (n : ℕ) :
    (∫ u in (0 : ℝ)..d, ∑ j ∈ Finset.range n, f (a + u + (j : ℝ) * d)) =
      ∫ x in a..(a + (n : ℝ) * d), f x := by
  rw [intervalIntegral.integral_finsetSum
    (fun j _ ↦ intervalIntegrable_grid_translate hf a d j)]
  have hterm (j : ℕ) :
      (∫ u in (0 : ℝ)..d, f (a + u + (j : ℝ) * d)) =
        ∫ x in (a + (j : ℝ) * d)..(a + ((j + 1 : ℕ) : ℝ) * d), f x := by
    have he : (fun u ↦ f (a + u + (j : ℝ) * d)) =
        (fun u ↦ f (u + (a + (j : ℝ) * d))) := by
      funext u
      congr 1
      ring
    rw [he, intervalIntegral.integral_comp_add_right]
    simp only [zero_add, Nat.cast_add, Nat.cast_one]
    congr 1
    ring
  simp_rw [hterm]
  have h := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun j : ℕ ↦ a + (j : ℝ) * d) (n := n) (fun _ _ ↦ hf.intervalIntegrable)
  simpa only [Nat.cast_zero, zero_mul, add_zero] using h

lemma exists_grid_sum_gt {f : ℝ → ℝ} (hf : Integrable f)
    (a : ℝ) {d η : ℝ} (hd : 0 < d) (n : ℕ)
    (harea : d * η < ∫ x in a..(a + (n : ℝ) * d), f x) :
    ∃ u ∈ Icc (0 : ℝ) d, η < ∑ j ∈ Finset.range n, f (a + u + (j : ℝ) * d) := by
  by_contra h
  push Not at h
  have hi : IntervalIntegrable
      (fun u ↦ ∑ j ∈ Finset.range n, f (a + u + (j : ℝ) * d)) volume 0 d := by
    have he : (∑ j ∈ Finset.range n, fun u ↦ f (a + u + (j : ℝ) * d)) =
        (fun u ↦ ∑ j ∈ Finset.range n, f (a + u + (j : ℝ) * d)) := by
      funext u
      simp only [Finset.sum_apply]
    rw [← he]
    exact IntervalIntegrable.sum (Finset.range n)
      (fun j _ ↦ intervalIntegrable_grid_translate hf a d j)
  have hb := intervalIntegral.integral_mono_on hd.le hi intervalIntegrable_const h
  rw [integral_finite_grid hf, intervalIntegral.integral_const] at hb
  simp only [sub_zero, smul_eq_mul] at hb
  exact (not_lt_of_ge hb) harea

lemma exists_positive_grid_subset {f : ℝ → ℝ} (hf : Integrable f)
    (hf0 : ∀ x, 0 ≤ f x) (a : ℝ) {d η : ℝ} (hd : 0 < d) (hη : 0 ≤ η) (n : ℕ)
    (harea : d * η < ∫ x in a..(a + (n : ℝ) * d), f x) :
    ∃ u ∈ Icc (0 : ℝ) d, ∃ s : Finset ℕ, s.Nonempty ∧ s ⊆ Finset.range n ∧
      (∀ j ∈ s, 0 < f (a + u + (j : ℝ) * d)) ∧
      η < ∑ j ∈ s, f (a + u + (j : ℝ) * d) := by
  classical
  obtain ⟨u, hu, hsum⟩ := exists_grid_sum_gt hf a hd n harea
  let s := (Finset.range n).filter (fun (j : ℕ) ↦ 0 < f (a + u + (j : ℝ) * d))
  have he : (∑ j ∈ s, f (a + u + (j : ℝ) * d)) =
      ∑ j ∈ Finset.range n, f (a + u + (j : ℝ) * d) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with hpos
    · rfl
    · exact (le_antisymm (le_of_not_gt hpos) (hf0 _)).symm
  refine ⟨u, hu, s, ?_, Finset.filter_subset _ _, ?_, by rwa [he]⟩
  · by_contra hs
    have hz : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    rw [← he, hz, Finset.sum_empty] at hsum
    exact (not_lt_of_ge hη) hsum
  · intro j hj
    exact (Finset.mem_filter.mp hj).2

end ExactOverlaps.WImprovement
