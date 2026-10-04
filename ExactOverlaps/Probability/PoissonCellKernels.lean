module

public import ExactOverlaps.Probability.PoissonKernels
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
# Interior-cell kernel identities

A block of atoms of diameter `d`, with neighboring gaps of lengths `l` and
`u`, is a cell when neither internal gap is cut and both neighboring gaps
are cut. The corresponding offset-length and exponential kernels have
exactly proportional integrals. Boundary blocks will use the versions with
one or both neighboring-cut factors omitted.
-/

@[expose] public section

open MeasureTheory Set

namespace ExactOverlaps.Poisson

/-- Exponential kernel for an interior block with two neighboring gaps. -/
noncomputable def cellSurvival (d l u t : ℝ) : ℝ :=
  Real.exp (-(d * t)) * (1 - Real.exp (-(l * t))) * (1 - Real.exp (-(u * t)))

/-- Offset length of intervals selecting exactly the interior block. -/
noncomputable def cellOffsetLength (d l u r : ℝ) : ℝ :=
  max (r - d) 0 - max (r - (d + l)) 0 - max (r - (d + u)) 0 +
    max (r - (d + l + u)) 0

/-- The positive-part expression equals the length of the actual offset intersection. -/
lemma cellOffsetLength_eq_intersection_length {d l u r : ℝ}
    (hl : 0 ≤ l) (hu : 0 ≤ u) :
    cellOffsetLength d l u r = max (min 0 (d + u - r) - max (-l) (d - r)) 0 := by
  unfold cellOffsetLength
  simp only [min_def, max_def]
  split_ifs <;> linarith

lemma cellOffsetLength_nonneg {d l u r : ℝ} (hl : 0 ≤ l) (hu : 0 ≤ u) :
    0 ≤ cellOffsetLength d l u r := by
  rw [cellOffsetLength_eq_intersection_length hl hu]
  exact le_max_right _ _

/-- Offsets whose half-open interval contains `0,d` and excludes `-l,d+u`. -/
def cellOffsets (d l u r : ℝ) : Set ℝ :=
  {a | -l < a ∧ a ≤ 0 ∧ d < a + r ∧ a + r ≤ d + u}

lemma cellOffsets_eq_Ioc (d l u r : ℝ) :
    cellOffsets d l u r = Ioc (max (-l) (d - r)) (min 0 (d + u - r)) := by
  ext a
  simp only [cellOffsets, Set.mem_ofPred_eq, mem_Ioc, max_lt_iff, le_min_iff]
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    exact ⟨⟨h₁, by linarith⟩, ⟨h₂, by linarith⟩⟩
  · rintro ⟨⟨h₁, h₃⟩, h₂, h₄⟩
    exact ⟨h₁, h₂, by linarith, by linarith⟩

/-- The offset kernel is the Lebesgue measure of the actual interval-selection event. -/
lemma volume_cellOffsets {d l u r : ℝ} (hl : 0 ≤ l) (hu : 0 ≤ u) :
    volume (cellOffsets d l u r) = ENNReal.ofReal (cellOffsetLength d l u r) := by
  rw [cellOffsets_eq_Ioc, Real.volume_Ioc, cellOffsetLength_eq_intersection_length hl hu]
  simp

lemma cellSurvival_expand (d l u t : ℝ) :
    cellSurvival d l u t = Real.exp (-(d * t)) - Real.exp (-((d + l) * t)) -
      Real.exp (-((d + u) * t)) + Real.exp (-((d + l + u) * t)) := by
  simp only [cellSurvival, add_mul, neg_add, Real.exp_add]
  ring

lemma integral_time_cellSurvival {d l u : ℝ} (hd : 0 < d) (hl : 0 ≤ l) (hu : 0 ≤ u) :
    (∫ t : ℝ in Ioi 0, t * cellSurvival d l u t) =
      1 / d ^ 2 - 1 / (d + l) ^ 2 - 1 / (d + u) ^ 2 + 1 / (d + l + u) ^ 2 := by
  have hdl : 0 < d + l := add_pos_of_pos_of_nonneg hd hl
  have hdu : 0 < d + u := add_pos_of_pos_of_nonneg hd hu
  have hdlu : 0 < d + l + u := add_pos_of_pos_of_nonneg hdl hu
  have hi (a : ℝ) (ha : 0 < a) :
      IntegrableOn (fun t : ℝ ↦ t * Real.exp (-(a * t))) (Ioi 0) := by
    simpa using integrableOn_pow_mul_exp ha 1
  have hi₁ : IntegrableOn (fun t : ℝ ↦
      t * Real.exp (-(d * t)) - t * Real.exp (-((d + l) * t))) (Ioi 0) := by
    exact ((hi d hd).sub (hi (d + l) hdl)).congr_fun
      (fun _ _ ↦ by simp) measurableSet_Ioi
  have hi₂ : IntegrableOn (fun t : ℝ ↦
      t * Real.exp (-(d * t)) - t * Real.exp (-((d + l) * t)) -
        t * Real.exp (-((d + u) * t))) (Ioi 0) := by
    exact (hi₁.sub (hi (d + u) hdu)).congr_fun
      (fun _ _ ↦ by simp) measurableSet_Ioi
  simp_rw [cellSurvival_expand, mul_add, mul_sub]
  rw [integral_add hi₂ (hi (d + l + u) hdlu),
    integral_sub hi₁ (hi (d + u) hdu),
    integral_sub (hi d hd) (hi (d + l) hdl),
    integral_time_mul_exp hd, integral_time_mul_exp hdl,
    integral_time_mul_exp hdu, integral_time_mul_exp hdlu]

lemma integral_cellOffsetLength {d l u : ℝ} (hd : 0 < d) (hl : 0 ≤ l) (hu : 0 ≤ u) :
    (∫ r : ℝ in Ioi 0, cellOffsetLength d l u r / r ^ 4) =
      1 / (6 * d ^ 2) - 1 / (6 * (d + l) ^ 2) - 1 / (6 * (d + u) ^ 2) +
        1 / (6 * (d + l + u) ^ 2) := by
  have hdl : 0 < d + l := add_pos_of_pos_of_nonneg hd hl
  have hdu : 0 < d + u := add_pos_of_pos_of_nonneg hd hu
  have hdlu : 0 < d + l + u := add_pos_of_pos_of_nonneg hdl hu
  have hi₁ : IntegrableOn (fun r : ℝ ↦
      max (r - d) 0 / r ^ 4 - max (r - (d + l)) 0 / r ^ 4) (Ioi 0) := by
    exact ((integrableOn_positive_offset_length hd).sub
      (integrableOn_positive_offset_length hdl)).congr_fun
        (fun _ _ ↦ by simp) measurableSet_Ioi
  have hi₂ : IntegrableOn (fun r : ℝ ↦
      max (r - d) 0 / r ^ 4 - max (r - (d + l)) 0 / r ^ 4 -
        max (r - (d + u)) 0 / r ^ 4) (Ioi 0) := by
    exact (hi₁.sub (integrableOn_positive_offset_length hdu)).congr_fun
      (fun _ _ ↦ by simp) measurableSet_Ioi
  simp only [cellOffsetLength, add_div, sub_div]
  rw [integral_add hi₂ (integrableOn_positive_offset_length hdlu),
    integral_sub hi₁ (integrableOn_positive_offset_length hdu),
    integral_sub (integrableOn_positive_offset_length hd)
      (integrableOn_positive_offset_length hdl),
    integral_positive_offset_length hd, integral_positive_offset_length hdl,
    integral_positive_offset_length hdu, integral_positive_offset_length hdlu]

/-- The exact analytic conversion from exponential cells to interval variance energy. -/
lemma integral_time_cellSurvival_eq_six_offset {d l u : ℝ}
    (hd : 0 < d) (hl : 0 ≤ l) (hu : 0 ≤ u) :
    (∫ t : ℝ in Ioi 0, t * cellSurvival d l u t) =
      6 * ∫ r : ℝ in Ioi 0, cellOffsetLength d l u r / r ^ 4 := by
  rw [integral_time_cellSurvival hd hl hu, integral_cellOffsetLength hd hl hu]
  simp only [one_div, mul_inv_rev]
  ring

end ExactOverlaps.Poisson
