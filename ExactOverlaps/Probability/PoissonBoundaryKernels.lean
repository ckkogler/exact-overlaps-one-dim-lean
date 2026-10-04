module

public import ExactOverlaps.Probability.PoissonCellKernels
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
# Boundary-cell kernel identities

A block touching one end of the finite support has only one neighboring-cut
factor. A block equal to the entire support has none. These are the boundary
counterparts of the interior-cell exponential and interval-offset kernels.
-/

@[expose] public section

open MeasureTheory Set

namespace ExactOverlaps.Poisson

noncomputable def boundarySurvival (d l t : ℝ) : ℝ :=
  Real.exp (-(d * t)) * (1 - Real.exp (-(l * t)))

noncomputable def boundaryOffsetLength (d l r : ℝ) : ℝ :=
  max (r - d) 0 - max (r - (d + l)) 0

lemma boundaryOffsetLength_eq_left_length {d l r : ℝ} (hl : 0 ≤ l) :
    boundaryOffsetLength d l r = max (min 0 (d + l - r) - (d - r)) 0 := by
  unfold boundaryOffsetLength
  simp only [min_def, max_def]
  split_ifs <;> linarith

lemma boundaryOffsetLength_eq_right_length {d l r : ℝ} (hl : 0 ≤ l) :
    boundaryOffsetLength d l r = max (-max (-l) (d - r)) 0 := by
  unfold boundaryOffsetLength
  simp only [max_def]
  split_ifs <;> linarith

lemma boundaryOffsetLength_nonneg {d l r : ℝ} (hl : 0 ≤ l) :
    0 ≤ boundaryOffsetLength d l r := by
  rw [boundaryOffsetLength_eq_left_length hl]
  exact le_max_right _ _

/-- The leftmost block has no lower exclusion condition on the window origin. -/
def leftBoundaryOffsets (d l r : ℝ) : Set ℝ :=
  {a | a ≤ 0 ∧ d < a + r ∧ a + r ≤ d + l}

/-- The rightmost block has no upper exclusion condition on the window endpoint. -/
def rightBoundaryOffsets (d l r : ℝ) : Set ℝ :=
  {a | -l < a ∧ a ≤ 0 ∧ d < a + r}

lemma volume_leftBoundaryOffsets {d l r : ℝ} (hl : 0 ≤ l) :
    volume (leftBoundaryOffsets d l r) = ENNReal.ofReal (boundaryOffsetLength d l r) := by
  have he : leftBoundaryOffsets d l r = Ioc (d - r) (min 0 (d + l - r)) := by
    ext a
    simp only [leftBoundaryOffsets, mem_ofPred_eq, mem_Ioc, le_min_iff]
    constructor
    · rintro ⟨h₁, h₂, h₃⟩
      exact ⟨by linarith, h₁, by linarith⟩
    · rintro ⟨h₂, h₁, h₃⟩
      exact ⟨h₁, by linarith, by linarith⟩
  rw [he, Real.volume_Ioc, boundaryOffsetLength_eq_left_length hl]
  simp

lemma volume_rightBoundaryOffsets {d l r : ℝ} (hl : 0 ≤ l) :
    volume (rightBoundaryOffsets d l r) = ENNReal.ofReal (boundaryOffsetLength d l r) := by
  have he : rightBoundaryOffsets d l r = Ioc (max (-l) (d - r)) 0 := by
    ext a
    simp only [rightBoundaryOffsets, mem_ofPred_eq, mem_Ioc, max_lt_iff]
    constructor
    · rintro ⟨h₁, h₂, h₃⟩
      exact ⟨⟨h₁, by linarith⟩, h₂⟩
    · rintro ⟨⟨h₁, h₃⟩, h₂⟩
      exact ⟨h₁, h₂, by linarith⟩
  rw [he, Real.volume_Ioc, boundaryOffsetLength_eq_right_length hl]
  simp

lemma boundarySurvival_expand (d l t : ℝ) :
    boundarySurvival d l t = Real.exp (-(d * t)) - Real.exp (-((d + l) * t)) := by
  simp only [boundarySurvival, add_mul, neg_add, Real.exp_add]
  ring

lemma integral_time_boundarySurvival {d l : ℝ} (hd : 0 < d) (hl : 0 ≤ l) :
    (∫ t : ℝ in Ioi 0, t * boundarySurvival d l t) = 1 / d ^ 2 - 1 / (d + l) ^ 2 := by
  have hdl := add_pos_of_pos_of_nonneg hd hl
  have hi (a : ℝ) (ha : 0 < a) :
      IntegrableOn (fun t : ℝ ↦ t * Real.exp (-(a * t))) (Ioi 0) := by
    simpa using integrableOn_pow_mul_exp ha 1
  simp_rw [boundarySurvival_expand, mul_sub]
  rw [integral_sub (hi d hd) (hi (d + l) hdl),
    integral_time_mul_exp hd, integral_time_mul_exp hdl]

lemma integral_boundaryOffsetLength {d l : ℝ} (hd : 0 < d) (hl : 0 ≤ l) :
    (∫ r : ℝ in Ioi 0, boundaryOffsetLength d l r / r ^ 4) =
      1 / (6 * d ^ 2) - 1 / (6 * (d + l) ^ 2) := by
  have hdl := add_pos_of_pos_of_nonneg hd hl
  simp only [boundaryOffsetLength, sub_div]
  rw [integral_sub (integrableOn_positive_offset_length hd)
    (integrableOn_positive_offset_length hdl),
    integral_positive_offset_length hd, integral_positive_offset_length hdl]

lemma integral_time_boundarySurvival_eq_six_offset {d l : ℝ}
    (hd : 0 < d) (hl : 0 ≤ l) :
    (∫ t : ℝ in Ioi 0, t * boundarySurvival d l t) =
      6 * ∫ r : ℝ in Ioi 0, boundaryOffsetLength d l r / r ^ 4 := by
  rw [integral_time_boundarySurvival hd hl, integral_boundaryOffsetLength hd hl]
  simp only [one_div, mul_inv_rev]
  ring

lemma integral_time_survival_eq_six_offset {d : ℝ} (hd : 0 < d) :
    (∫ t : ℝ in Ioi 0, t * Real.exp (-(d * t))) =
      6 * ∫ r : ℝ in Ioi 0, max (r - d) 0 / r ^ 4 := by
  rw [integral_time_mul_exp hd, integral_positive_offset_length hd]
  simp only [one_div, mul_inv_rev]
  ring

end ExactOverlaps.Poisson
