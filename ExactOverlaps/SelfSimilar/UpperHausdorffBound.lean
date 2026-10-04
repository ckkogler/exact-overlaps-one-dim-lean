module

public import ExactOverlaps.SelfSimilar.HausdorffCovering
public import ExactOverlaps.SelfSimilar.LowerHausdorffBound

/-!
Identification of the standard lower Hausdorff dimension of an
exact-dimensional real probability. A positive good set has finite
Hausdorff measure; its Hausdorff-measure Borel hull supplies a measurable
competitor in the definition of lower Hausdorff dimension.
-/

@[expose] public section

open MeasureTheory Filter Metric Set
open scoped ENNReal NNReal Topology

namespace ExactOverlaps

theorem HasExactDimension.lowerHausdorffDimension_le_nnreal {μ : Measure ℝ}
    [IsProbabilityMeasure μ] {d : ℝ} (hd : HasExactDimension μ d) (s : ℝ≥0)
    (hds : d < (s : ℝ)) : lowerHausdorffDimension μ ≤ (s : ℝ≥0∞) := by
  let ε : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  let E : ℕ → Set ℝ := fun n ↦ {x | ∀ r : ℝ, 0 < r → r ≤ ε n →
    (ENNReal.ofReal r) ^ (s : ℝ) ≤ μ (closedBall x r)}
  have hcover : ∀ᵐ x ∂μ, ∃ n, x ∈ E n := by
    filter_upwards [hd, ae_closedBall_measure_pos μ] with x hx hp
    obtain ⟨δ, hδ, hb⟩ := exists_uniform_ball_lower_power μ x hp hds hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
    exact ⟨n, fun r hr hre ↦ hb r hr (hre.trans hn.le)⟩
  have hex : ∃ n, 0 < μ (E n) := by
    by_contra h
    have hn : ∀ n, μ (E n) = 0 := by
      intro n
      exact le_antisymm (le_of_not_gt (fun hh ↦ h ⟨n, hh⟩)) bot_le
    have ha : ∀ᵐ x ∂μ, ∀ n, x ∉ E n := by
      apply ae_all_iff.mpr
      intro n
      change (E n)ᶜ ∈ ae μ
      rw [mem_ae_iff, compl_compl]
      exact hn n
    obtain ⟨x, ⟨n, hxn⟩, hx⟩ := (hcover.and ha).exists
    exact hx n hxn
  obtain ⟨n, hn⟩ := hex
  have hH : Measure.hausdorffMeasure (s : ℝ) (E n) < ⊤ :=
    hausdorffMeasure_lt_top_of_ball_lower_bound μ (E n) s.coe_nonneg
      (by dsimp [ε]; positivity) (fun _ hx ↦ hx)
  let B := toMeasurable (Measure.hausdorffMeasure (s : ℝ)) (E n)
  have hBm : MeasurableSet B := measurableSet_toMeasurable _ _
  have hBpos : 0 < μ B := hn.trans_le (measure_mono (subset_toMeasurable _ _))
  apply (lowerHausdorffDimension_le_dimH μ hBm hBpos).trans
  apply dimH_le_of_hausdorffMeasure_ne_top
  change Measure.hausdorffMeasure (s : ℝ) (toMeasurable (Measure.hausdorffMeasure (s : ℝ)) (E n)) ≠ ⊤
  rw [measure_toMeasurable]
  exact hH.ne

theorem HasExactDimension.lowerHausdorffDimension_eq {μ : Measure ℝ}
    [IsProbabilityMeasure μ] {d : ℝ} (hd : HasExactDimension μ d) :
    lowerHausdorffDimension μ = ENNReal.ofReal d := by
  apply le_antisymm _ hd.le_lowerHausdorffDimension
  apply le_of_not_gt
  intro h
  obtain ⟨s, hslo, hshi⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
  have hds : d < (s : ℝ) := by
    by_cases hd0 : 0 ≤ d
    · exact (ENNReal.ofReal_lt_coe_iff hd0).mp hslo
    · exact (lt_of_not_ge hd0).trans_le s.coe_nonneg
  exact hshi.not_ge (hd.lowerHausdorffDimension_le_nnreal s hds)

end ExactOverlaps
