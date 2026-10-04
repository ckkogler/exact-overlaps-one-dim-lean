/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic

/-!
Recursive selection of positive scales and blocks. The selection lemma only
uses its stated availability hypothesis; the main theorem supplies it from
the proved uniform improvement proposition.
-/

@[expose] public section

open Filter
open scoped Topology

namespace ExactOverlaps.MainTheorem

/-- Uniform availability at every relative scale supplies an infinite sequence
with the exact adjacent separation used by stopped-block concatenation. -/
theorem exists_separated_sequence {B : Type*}
    (P : B → ℝ → Prop) (L : B → ℝ → ℝ → Prop)
    {a : ℝ} (ha : 0 < a)
    (h : ∀ ε : ℝ, 0 < ε → ∃ b : B, ∃ r : ℝ, 0 < r ∧ P b r ∧ L b ε r) :
    ∃ b : ℕ → B, ∃ r : ℕ → ℝ, (∀ n, 0 < r n) ∧ (∀ n, P (b n) (r n)) ∧
      L (b 0) 1 (r 0) ∧ ∀ n, L (b (n + 1)) (a * r n) (r (n + 1)) := by
  classical
  let X := {z : B × ℝ // 0 < z.2 ∧ P z.1 z.2}
  have hs (ε : ℝ) (hε : 0 < ε) : ∃ x : X, L x.val.1 ε x.val.2 := by
    obtain ⟨b, r, hr, hP, hR⟩ := h ε hε
    exact ⟨⟨(b, r), hr, hP⟩, hR⟩
  let chooseAt (ε : ℝ) (hε : 0 < ε) : X := (hs ε hε).choose
  have hchoose (ε : ℝ) (hε : 0 < ε) :
      L (chooseAt ε hε).val.1 ε (chooseAt ε hε).val.2 := (hs ε hε).choose_spec
  let next (x : X) : X := chooseAt (a * x.val.2) (mul_pos ha x.property.1)
  let x : ℕ → X := fun n ↦ next^[n] (chooseAt 1 zero_lt_one)
  refine ⟨fun n ↦ (x n).val.1, fun n ↦ (x n).val.2,
    fun n ↦ (x n).property.1, fun n ↦ (x n).property.2, ?_, ?_⟩
  · exact hchoose 1 zero_lt_one
  · intro n
    change L (x (n + 1)).val.1 (a * (x n).val.2) (x (n + 1)).val.2
    have he : x (n + 1) = next (x n) := Function.iterate_succ_apply' next n _
    rw [he]
    exact hchoose (a * (x n).val.2) (mul_pos ha (x n).property.1)

/-- A positive sequence with a fixed geometric contraction tends to zero. -/
theorem geometrically_decreasing_scales_tendsto_zero
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (r : ℕ → ℝ)
    (hr : ∀ n, 0 < r n) (hstep : ∀ n, r (n + 1) ≤ a * r n) :
    Tendsto r atTop (𝓝 0) := by
  have hbound (n : ℕ) : r n ≤ a ^ n * r 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        r (n + 1) ≤ a * r n := hstep n
        _ ≤ a * (a ^ n * r 0) := mul_le_mul_of_nonneg_left ih ha.le
        _ = a ^ (n + 1) * r 0 := by rw [pow_succ]; ring
  have hzero : Tendsto (fun n : ℕ ↦ a ^ n * r 0) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one ha.le ha1).mul_const (r 0)
  exact squeeze_zero (fun n ↦ (hr n).le) hbound hzero

end ExactOverlaps.MainTheorem
