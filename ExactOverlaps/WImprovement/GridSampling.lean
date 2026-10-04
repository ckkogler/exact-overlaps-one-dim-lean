/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.WImprovement.GridAveraging
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Sampling compact logarithmic profiles

A compactly supported nonnegative profile with sufficiently large integral
has a finite nonempty sample on one translated grid. Every retained point
lies strictly inside the support window. Exponentiating gives the exact
multiplicative separation required for independent block concatenation.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace ExactOverlaps.WImprovement

lemma exists_compact_grid_sample {f : ℝ → ℝ} (hf : Integrable f)
    (hf0 : ∀ x, 0 ≤ f x) (a b : ℝ)
    (hzero : ∀ x, x ≤ a ∨ b ≤ x → f x = 0)
    {d η : ℝ} (hd : 0 < d) (hη : 0 ≤ η) (harea : d * η < ∫ x, f x) :
    ∃ u ∈ Icc (0 : ℝ) d, ∃ s : Finset ℕ, s.Nonempty ∧
      (∀ j ∈ s, a < a + u + (j : ℝ) * d ∧ a + u + (j : ℝ) * d < b) ∧
      η < ∑ j ∈ s, f (a + u + (j : ℝ) * d) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max 0 ((b - a) / d))
  have hn0 : 0 < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
  have hb : b < a + (n : ℝ) * d := by
    have h := (div_lt_iff₀ hd).mp (lt_of_le_of_lt (le_max_right _ _) hn)
    linarith
  have hu : a ≤ a + (n : ℝ) * d := by nlinarith
  have he : (∫ x in a..(a + (n : ℝ) * d), f x) = ∫ x, f x := by
    rw [intervalIntegral.integral_of_le hu]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    by_cases hax : a < x
    · have hupper : a + (n : ℝ) * d < x := lt_of_not_ge (fun hxu ↦ hx ⟨hax, hxu⟩)
      exact hzero x (Or.inr (hb.trans hupper).le)
    · exact hzero x (Or.inl (le_of_not_gt hax))
  obtain ⟨u, huint, s, hs, _, hpos, hsum⟩ :=
    exists_positive_grid_subset hf hf0 a hd hη n (by rwa [he])
  refine ⟨u, huint, s, hs, ?_, hsum⟩
  intro j hj
  have hp := hpos j hj
  constructor
  · by_contra h
    have := hzero (a + u + (j : ℝ) * d) (Or.inl (le_of_not_gt h))
    linarith
  · by_contra h
    have := hzero (a + u + (j : ℝ) * d) (Or.inr (le_of_not_gt h))
    linarith

lemma exp_grid_separation (a u : ℝ) {d : ℝ} (hd : 0 ≤ d)
    {j k : ℕ} (hjk : j < k) :
    Real.exp d * Real.exp (a + u + (j : ℝ) * d) ≤
      Real.exp (a + u + (k : ℝ) * d) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  have h : (j : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hjk
  nlinarith

lemma exp_grid_strictMono (a u : ℝ) {d : ℝ} (hd : 0 < d) :
    StrictMono (fun j : ℕ ↦ Real.exp (a + u + (j : ℝ) * d)) := by
  intro j k hjk
  apply Real.exp_lt_exp.mpr
  have h : (j : ℝ) < (k : ℝ) := by exact_mod_cast hjk
  nlinarith

end ExactOverlaps.WImprovement
