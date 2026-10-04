module

public import ExactOverlaps.SelfSimilar.BallLocalDimension
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
Uniform small-ball power estimates from the standard local-dimension
limit. The upper estimate includes radius zero, with its null mass proved
by continuity of the positive power bound at zero.
-/

@[expose] public section

open MeasureTheory Filter Metric
open scoped Topology ENNReal

namespace ExactOverlaps

theorem ball_mass_le_rpow_of_ratio_ge (μ : Measure ℝ) [IsFiniteMeasure μ]
    (x : ℝ) {r s : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hpos : 0 < μ (closedBall x r))
    (h : s ≤ Real.log (μ (closedBall x r)).toReal / Real.log r) :
    μ (closedBall x r) ≤ (ENNReal.ofReal r) ^ s := by
  rw [ENNReal.ofReal_rpow_of_pos hr,
    ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (Real.rpow_nonneg hr.le s)]
  rw [Real.rpow_def_of_pos hr]
  have hmpos := ENNReal.toReal_pos hpos.ne' (measure_ne_top μ _)
  rw [← Real.exp_log hmpos]
  apply Real.exp_le_exp.mpr
  have hh := (le_div_iff_of_neg (Real.log_neg hr hr1)).mp h
  linarith

theorem rpow_le_ball_mass_of_ratio_le (μ : Measure ℝ) [IsFiniteMeasure μ]
    (x : ℝ) {r s : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hpos : 0 < μ (closedBall x r))
    (h : Real.log (μ (closedBall x r)).toReal / Real.log r ≤ s) :
    (ENNReal.ofReal r) ^ s ≤ μ (closedBall x r) := by
  rw [ENNReal.ofReal_rpow_of_pos hr, ← ENNReal.ofReal_toReal (measure_ne_top μ _)]
  apply ENNReal.ofReal_le_ofReal
  rw [Real.rpow_def_of_pos hr]
  have hmpos := ENNReal.toReal_pos hpos.ne' (measure_ne_top μ _)
  rw [← Real.exp_log hmpos]
  apply Real.exp_le_exp.mpr
  have hh := (div_le_iff_of_neg (Real.log_neg hr hr1)).mp h
  linarith

theorem exists_uniform_ball_upper_power (μ : Measure ℝ) [IsFiniteMeasure μ] (x : ℝ)
    (hpos : ∀ r : ℝ, 0 < r → 0 < μ (closedBall x r)) {d s : ℝ}
    (hs : 0 < s) (hsd : s < d)
    (hd : Tendsto (fun r : ℝ ↦ Real.log (μ (closedBall x r)).toReal / Real.log r)
      (𝓝[>] 0) (𝓝 d)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 ≤ r → r ≤ ε →
      μ (closedBall x r) ≤ (ENNReal.ofReal r) ^ s := by
  have he := (hd.eventually (lt_mem_nhds hsd)).and
    ((gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds)
  obtain ⟨δ, hδ, hδset⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp he
  have hδpos : 0 < δ := hδ
  let ε := δ / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hb : ∀ r : ℝ, 0 < r → r ≤ ε → μ (closedBall x r) ≤ (ENNReal.ofReal r) ^ s := by
    intro r hr hre
    have hh := hδset (show r ∈ Set.Ioo 0 δ from ⟨hr, by dsimp [ε] at hre; linarith⟩)
    exact ball_mass_le_rpow_of_ratio_ge μ x hr hh.2 (hpos r hr) hh.1.le
  refine ⟨ε, hε, fun r hr hre ↦ ?_⟩
  rcases hr.eq_or_lt with rfl | hrp
  · have hn : ∀ n : ℕ, μ (closedBall x 0) ≤
        (ENNReal.ofReal (ε * (1 / 2 : ℝ) ^ n)) ^ s := by
      intro n
      have hnp : 0 < ε * (1 / 2 : ℝ) ^ n := mul_pos hε (pow_pos (by norm_num) n)
      apply (measure_mono (closedBall_subset_closedBall hnp.le)).trans
      apply hb _ hnp
      exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (by norm_num) (by norm_num)) hε.le).trans_eq (mul_one ε)
    have hlim : Tendsto (fun n : ℕ ↦ ε * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).const_mul ε
    have hp := (ENNReal.continuous_ofReal.tendsto 0 |>.comp hlim).ennrpow_const s
    simp only [ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos hs] at hp ⊢
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds hp hn
  · exact hb r hrp hre

theorem exists_uniform_ball_lower_power (μ : Measure ℝ) [IsFiniteMeasure μ] (x : ℝ)
    (hpos : ∀ r : ℝ, 0 < r → 0 < μ (closedBall x r)) {d s : ℝ} (hds : d < s)
    (hd : Tendsto (fun r : ℝ ↦ Real.log (μ (closedBall x r)).toReal / Real.log r)
      (𝓝[>] 0) (𝓝 d)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r ≤ ε →
      (ENNReal.ofReal r) ^ s ≤ μ (closedBall x r) := by
  have he := (hd.eventually (gt_mem_nhds hds)).and
    ((gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds)
  obtain ⟨δ, hδ, hδset⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp he
  have hδpos : 0 < δ := hδ
  refine ⟨δ / 2, by positivity, fun r hr hre ↦ ?_⟩
  have hh := hδset (show r ∈ Set.Ioo 0 δ from ⟨hr, by linarith⟩)
  exact rpow_le_ball_mass_of_ratio_le μ x hr hh.2 (hpos r hr) hh.1.le

end ExactOverlaps
