module

public import ExactOverlaps.SelfSimilar.Definitions
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
Adapted from Constantin Kogler’s 0BSD LpSelfSimilar formalization (2026).

Compact support is a consequence of stationarity, not a hypothesis. A uniform
contraction sends each sufficiently far tail into a strictly farther inverse
tail. Stationarity makes the masses increase along these tails, whereas finite
measure and continuity from above force their limit to be zero.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped ENNReal NNReal BigOperators

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι]

/-- Every finite stationary measure is carried by an explicitly bounded closed ball. -/
lemma exists_closedBall_full_measure (S : System ι) {ν : Measure (ℝ)}
    [IsFiniteMeasure ν] (hν : S.IsStationary ν) :
    ∃ R : ℝ, 0 < R ∧ ν (closedBall (0 : ℝ) R)ᶜ = 0 := by
  obtain ⟨c, M, hc, hc1, hM, hratio, hshift⟩ := S.exists_uniform_bounds
  let B := M / (1 - c)
  let a := c⁻¹
  have hB : 0 ≤ B := div_nonneg hM (sub_pos.mpr hc1).le
  have ha : 1 < a := (one_lt_inv₀ hc).mpr hc1
  have hBfix : c * B + M = B := by
    have h := mul_div_cancel₀ M (sub_pos.mpr hc1).ne'
    change (1 - c) * B = M at h
    linarith
  let T : ℕ → Set (ℝ) := fun n ↦ {x | B + a ^ n < |x|}
  have hmeas (n : ℕ) : MeasurableSet (T n) :=
    (isOpen_lt continuous_const continuous_abs).measurableSet
  have hanti : Antitone T := by
    intro m n hmn x hx
    have hp : a ^ m ≤ a ^ n := pow_le_pow_right₀ ha.le hmn
    change B + a ^ n < |x| at hx
    change B + a ^ m < |x|
    linarith
  have hstep (n : ℕ) : ν (T n) ≤ ν (T (n + 1)) := by
    apply S.measure_le_of_preimages_subset hν (hmeas n)
    intro i x hx
    have hnorm : |S.map i x| ≤ c * |x| + M :=
      (S.map i).abs_apply_le x |>.trans
        (add_le_add (mul_le_mul_of_nonneg_right (hratio i) (abs_nonneg x)) (hshift i))
    have hp : c * a ^ (n + 1) = a ^ n := by
      rw [pow_succ]
      calc
        c * (a ^ n * a) = a ^ n * (c * c⁻¹) := by dsimp [a]; ring
        _ = a ^ n := by rw [mul_inv_cancel₀ hc.ne', mul_one]
    change B + a ^ n < |S.map i x| at hx
    change B + a ^ (n + 1) < |x|
    nlinarith
  have hmass (n : ℕ) : ν (T 0) ≤ ν (T n) := by
    induction n with
    | zero => rfl
    | succ n ih => exact ih.trans (hstep n)
  have hinter : (⋂ n, T n) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt |x| ha
    have hx := mem_iInter.mp hx n
    change B + a ^ n < |x| at hx
    linarith
  have hzero : ν (T 0) = 0 := by
    apply le_antisymm ?_ zero_le
    have h := le_iInf hmass
    rw [← hanti.measure_iInter (fun n ↦ (hmeas n).nullMeasurableSet)
      ⟨0, measure_ne_top ν _⟩, hinter, measure_empty] at h
    exact h
  refine ⟨B + 1, by linarith, ?_⟩
  have heq : (closedBall (0 : ℝ) (B + 1))ᶜ = T 0 := by
    ext x
    simp [T, mem_closedBall]
  rw [heq]
  exact hzero

/-- A compact full-measure set with a positive diameter bound at least one.
Keeping this bound replaces the paper's diameter-one normalization. -/
lemma exists_compact_full_measure (S : System ι) {ν : Measure (ℝ)}
    [IsProbabilityMeasure ν] (hν : S.IsStationary ν) :
    ∃ K : Set (ℝ), IsCompact K ∧ ν Kᶜ = 0 ∧ ν K = 1 ∧
      ∃ D : ℝ, 1 ≤ D ∧ ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D := by
  obtain ⟨R, hR, hfull⟩ := S.exists_closedBall_full_measure hν
  refine ⟨closedBall (0 : ℝ) R, isCompact_closedBall _ _, hfull,
    (measure_of_measure_compl_eq_zero hfull).trans (measure_univ),
    max 1 (2 * R), le_max_left _ _, ?_⟩
  intro x hx y hy
  calc
    dist x y ≤ dist x 0 + dist y 0 := dist_triangle_right x y 0
    _ ≤ 2 * R := by have := mem_closedBall.mp hx; have := mem_closedBall.mp hy; linarith
    _ ≤ max 1 (2 * R) := le_max_right _ _

end ExactOverlaps.SelfSimilar.System
