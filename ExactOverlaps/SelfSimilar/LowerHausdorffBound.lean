module

public import ExactOverlaps.SelfSimilar.MassDistribution
public import ExactOverlaps.SelfSimilar.BallPowerBounds

/-!
The local dimension is a lower bound for the lower Hausdorff dimension
of an exact-dimensional finite real measure. Uniform small-ball bounds
are exhausted by countably many good sets, without assuming those sets
are measurable.
-/

@[expose] public section

open MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology

namespace ExactOverlaps

theorem HasExactDimension.nnreal_le_lowerHausdorffDimension {μ : Measure ℝ}
    [IsFiniteMeasure μ] {d : ℝ} (hd : HasExactDimension μ d) (s : ℝ≥0)
    (hs : 0 < (s : ℝ)) (hsd : (s : ℝ) < d) :
    (s : ℝ≥0∞) ≤ lowerHausdorffDimension μ := by
  let ε : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  let E : ℕ → Set ℝ := fun n ↦ {x | ∀ r : ℝ, 0 ≤ r → r ≤ ε n →
    μ (closedBall x r) ≤ (ENNReal.ofReal r) ^ (s : ℝ)}
  apply lowerHausdorffDimension_ge_of_ball_good_sets μ s E ε (fun n ↦ by dsimp [ε]; positivity)
    (fun _ _ hx ↦ hx)
  filter_upwards [hd, ae_closedBall_measure_pos μ] with x hx hp
  obtain ⟨δ, hδ, hb⟩ := exists_uniform_ball_upper_power μ x hp hs hsd hx
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  exact ⟨n, fun r hr hre ↦ hb r hr (hre.trans hn.le)⟩

theorem HasExactDimension.le_lowerHausdorffDimension {μ : Measure ℝ}
    [IsFiniteMeasure μ] {d : ℝ} (hd : HasExactDimension μ d) :
    ENNReal.ofReal d ≤ lowerHausdorffDimension μ := by
  apply le_of_not_gt
  intro h
  obtain ⟨s, hslo, hshi⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
  have hspos : 0 < (s : ℝ) := by
    have hh : (0 : ℝ≥0∞) < s := lt_of_le_of_lt bot_le hslo
    exact_mod_cast hh
  have hsd : (s : ℝ) < d := ENNReal.coe_lt_ofReal.mp hshi
  exact hslo.not_ge (hd.nnreal_le_lowerHausdorffDimension s hspos hsd)

end ExactOverlaps
