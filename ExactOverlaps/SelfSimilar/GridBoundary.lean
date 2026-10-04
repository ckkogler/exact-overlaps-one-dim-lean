module

public import ExactOverlaps.SelfSimilar.NonatomicIntervals
public import ExactOverlaps.SelfSimilar.Similarity
public import Mathlib.Data.Int.Interval

/-!
Neighborhoods of all integer grid boundaries. The estimates retain
arbitrary grid translations and signed affine multipliers. Compact support
reduces the infinitely many boundaries to a uniformly bounded finite set.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped ENNReal BigOperators

namespace ExactOverlaps

def integerGridNeighborhood (ρ : ℝ) : Set ℝ :=
  {x | ∃ k : ℤ, |x - k| ≤ ρ}

theorem measurableSet_integerGridNeighborhood (ρ : ℝ) :
    MeasurableSet (integerGridNeighborhood ρ) := by
  have he : integerGridNeighborhood ρ = ⋃ k : ℤ, {x : ℝ | |x - k| ≤ ρ} := by
    ext x
    simp only [integerGridNeighborhood, mem_ofPred_eq, mem_iUnion]
  rw [he]
  exact MeasurableSet.iUnion (fun k ↦ isClosed_le
    ((continuous_id.sub continuous_const).abs) continuous_const |>.measurableSet)

theorem mem_integerGridNeighborhood_of_dist_le {x y ρ δ : ℝ}
    (hx : x ∈ integerGridNeighborhood ρ) (hxy : |y - x| ≤ δ) :
    y ∈ integerGridNeighborhood (ρ + δ) := by
  obtain ⟨k, hk⟩ := hx
  refine ⟨k, ?_⟩
  have h := abs_sub_le y x (k : ℝ)
  linarith

theorem mem_integerGridNeighborhood_of_floor_ne {x y ρ : ℝ}
    (hxy : |x - y| ≤ ρ) (hne : ⌊x⌋ ≠ ⌊y⌋) :
    x ∈ integerGridNeighborhood ρ := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨⌊x⌋ + 1, ?_⟩
    have hfloor : (⌊x⌋ : ℝ) + 1 ≤ y := by
      have hz : ⌊x⌋ + 1 ≤ ⌊y⌋ := by omega
      have hz' : (⌊x⌋ : ℝ) + 1 ≤ (⌊y⌋ : ℝ) := by exact_mod_cast hz
      exact hz'.trans (Int.floor_le y)
    have hx := Int.lt_floor_add_one x
    simp only [Int.cast_add, Int.cast_one]
    rw [abs_of_nonpos (by linarith)]
    have h := (abs_le.mp hxy).1
    linarith
  · refine ⟨⌊x⌋, ?_⟩
    have hy : y < (⌊x⌋ : ℝ) := by
      have hz : ⌊y⌋ + 1 ≤ ⌊x⌋ := by omega
      have hz' : (⌊y⌋ : ℝ) + 1 ≤ (⌊x⌋ : ℝ) := by exact_mod_cast hz
      exact (Int.lt_floor_add_one y).trans_le hz'
    rw [abs_of_nonneg (sub_nonneg.mpr (Int.floor_le x))]
    have h := (abs_le.mp hxy).2
    linarith

theorem affine_grid_label_bound {a b x ρ : ℝ} {N : ℕ}
    (ha : |a| ≤ 1) (hx : |x| + 2 ≤ N) (hρ : ρ ≤ 1)
    {k : ℤ} (hk : |a * x + b - k| ≤ ρ) :
    k - ⌊b⌋ ∈ Finset.Icc (-(N : ℤ)) N := by
  have ha0 := abs_nonneg a
  have hx0 := abs_nonneg x
  have hprod : |a * x| ≤ |x| := by
    rw [abs_mul]
    nlinarith
  have hfloorlo := Int.floor_le b
  have hfloorhi := Int.lt_floor_add_one b
  have hax := abs_le.mp hprod
  have hdist := abs_le.mp hk
  have hl : -(N : ℝ) ≤ (k : ℝ) - ⌊b⌋ := by linarith
  have hu : (k : ℝ) - ⌊b⌋ ≤ N := by linarith
  simp only [Finset.mem_Icc]
  constructor
  · exact_mod_cast hl
  · exact_mod_cast hu

theorem affine_gridNeighborhood_measure_le (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a b ρ δ a₀ : ℝ} {N : ℕ} {η : ℝ≥0∞}
    (ha₀ : 0 < a₀) (halower : a₀ ≤ |a|) (haupper : |a| ≤ 1)
    (hρ : ρ ≤ 1) (hδ : 0 ≤ δ) (hscale : ρ ≤ a₀ * δ)
    (hsupport : ∀ᵐ x : ℝ ∂μ, |x| + 2 ≤ (N : ℝ))
    (hsmall : ∀ x : ℝ, μ (closedBall x δ) ≤ η) :
    μ ((fun x : ℝ ↦ a * x + b) ⁻¹' integerGridNeighborhood ρ) ≤
      (2 * N + 1 : ℕ) * η := by
  classical
  have hapos : 0 < |a| := ha₀.trans_le halower
  have ha : a ≠ 0 := abs_pos.mp hapos
  let J : Finset ℤ := Finset.Icc (-(N : ℤ)) N
  let E (j : ℤ) : Set ℝ := {x | |a * x + b - (⌊b⌋ + j : ℤ)| ≤ ρ}
  have hcover : μ ((fun x : ℝ ↦ a * x + b) ⁻¹' integerGridNeighborhood ρ) ≤
      μ (⋃ j ∈ J, E j) := by
    apply measure_mono_ae
    filter_upwards [hsupport] with x hx
    rintro ⟨k, hk⟩
    refine mem_iUnion.mpr ⟨k - ⌊b⌋, mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · exact affine_grid_label_bound haupper hx hρ hk
    · simpa only [E, mem_ofPred_eq, add_sub_cancel] using hk
  have hmass (j : ℤ) : μ (E j) ≤ η := by
    apply (measure_mono (show E j ⊆ closedBall (((⌊b⌋ + j : ℤ) - b) / a) δ from ?_)).trans
      (hsmall _)
    intro x hx
    have he : a * (x - (((⌊b⌋ + j : ℤ) : ℝ) - b) / a) =
        a * x + b - (⌊b⌋ + j : ℤ) := by field_simp; ring
    rw [mem_closedBall, Real.dist_eq]
    apply (mul_le_mul_iff_right₀ hapos).mp
    calc
      |a| * |x - (((⌊b⌋ + j : ℤ) : ℝ) - b) / a| =
          |a * x + b - (⌊b⌋ + j : ℤ)| := by rw [← abs_mul, he]
      _ ≤ ρ := hx
      _ ≤ a₀ * δ := hscale
      _ ≤ |a| * δ := mul_le_mul_of_nonneg_right halower hδ
  calc
    _ ≤ μ (⋃ j ∈ J, E j) := hcover
    _ ≤ ∑ j ∈ J, μ (E j) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ J, η := Finset.sum_le_sum (fun j _ ↦ hmass j)
    _ = (2 * N + 1 : ℕ) * η := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hcard : J.card = 2 * N + 1 := by
        dsimp [J]
        rw [Int.card_Icc]
        omega
      rw [hcard]

end ExactOverlaps
