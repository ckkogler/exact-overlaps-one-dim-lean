module

public import ExactOverlaps.SelfSimilar.CodingInformationAverages

/-!
Ball masses along the coding contraction scales. The conditional branch
ball mass has an exact recursive formula, and a fixed large initial
radius gives mass one at every coded point.
-/

@[expose] public section

open MeasureTheory Filter Metric
open scoped ENNReal Topology

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

noncomputable def prefixBallMass (S : System ι) (r : ℝ) (n : ℕ) (ω : ℕ → ι) : ℝ≥0∞ :=
  S.codingMeasure (closedBall (S.coding ω) (|S.prefixRatio n ω| * r))

omit [MeasurableSingletonClass ι] in
theorem branch_prefixBallMass (S : System ι) (r : ℝ) (n : ℕ) (ω : ℕ → ι) :
    S.branchMeasure S.codingMeasure (ω 0)
      (closedBall (S.coding ω) (|S.prefixRatio (n + 1) ω| * r)) =
        (S.weight (ω 0) : ℝ≥0∞) * S.prefixBallMass r n (Bernoulli.shift ω) := by
  rw [S.coding_shift ω, prefixRatio_succ_shift, abs_mul, mul_assoc,
    branchMeasure_closedBall_scaled]
  rfl

theorem exists_coding_full_ball_radius (S : System ι) :
    ∃ r : ℝ, 0 < r ∧ ∀ ω : ℕ → ι, S.codingMeasure (closedBall (S.coding ω) r) = 1 := by
  obtain ⟨c, M, hc, hc1, hM, hmax, hshift⟩ := S.exists_uniform_bounds
  let B := M / (1 - c)
  have hB : 0 ≤ B := div_nonneg hM (sub_pos.mpr hc1).le
  refine ⟨2 * B + 1, by positivity, ?_⟩
  intro ω
  rw [codingMeasure, Measure.map_apply S.measurable_coding measurableSet_closedBall]
  have heq : S.coding ⁻¹' closedBall (S.coding ω) (2 * B + 1) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro v
    change dist (S.coding v) (S.coding ω) ≤ 2 * B + 1
    rw [Real.dist_eq]
    have hh := abs_sub_le (S.coding v) 0 (S.coding ω)
    simp only [sub_zero, zero_sub, abs_neg] at hh
    have hv := S.abs_coding_le hc.le hc1 hmax hshift v
    have hω := S.abs_coding_le hc.le hc1 hmax hshift ω
    change |S.coding v| ≤ B at hv
    change |S.coding ω| ≤ B at hω
    linarith
  rw [heq, measure_univ]

theorem ae_prefixBallMass_pos (S : System ι) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂Bernoulli.sequenceLaw S.alphabetLaw.toMeasure,
      ∀ n : ℕ, 0 < S.prefixBallMass r n ω := by
  have h : ∀ᵐ ω ∂Bernoulli.sequenceLaw S.alphabetLaw.toMeasure,
      ∀ R : ℝ, 0 < R → 0 < S.codingMeasure (closedBall (S.coding ω) R) :=
    ae_of_ae_map S.measurable_coding.aemeasurable (ae_closedBall_measure_pos S.codingMeasure)
  filter_upwards [h] with ω hω
  intro n
  exact hω _ (mul_pos (abs_pos.mpr (S.prefixRatio_ne_zero n ω)) hr)

theorem prefixBallMass_ne_top (S : System ι) (r : ℝ) (n : ℕ) (ω : ℕ → ι) :
    S.prefixBallMass r n ω ≠ ⊤ := measure_ne_top _ _

end ExactOverlaps.SelfSimilar.System
