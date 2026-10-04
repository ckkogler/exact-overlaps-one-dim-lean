module

public import ExactOverlaps.SelfSimilar.BallPowerBounds
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
public import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
Finite Hausdorff measure from a uniform lower small-ball mass estimate.
The Besicovitch covering used here covers the entire good set, including
any exceptional subset of zero measure.
-/

@[expose] public section

open MeasureTheory Metric Set Filter
open scoped Topology ENNReal

namespace ExactOverlaps

theorem ediam_closedBall_le_two_mul (x r : ℝ) :
    Metric.ediam (closedBall x r) ≤ 2 * ENNReal.ofReal r := by
  have hh : Metric.ediam (closedBall x r) ≤ ENNReal.ofReal (2 * r) := by
    apply Metric.ediam_le_of_forall_dist_le
    intro a ha b hb
    have ht := dist_triangle_right a b x
    change dist a x ≤ r at ha
    change dist b x ≤ r at hb
    linarith
  simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat] using hh

theorem hausdorffMeasure_lt_top_of_ball_lower_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    (E : Set ℝ) {s ε : ℝ} (hs : 0 ≤ s) (hε : 0 < ε)
    (hball : ∀ x ∈ E, ∀ r : ℝ, 0 < r → r ≤ ε →
      (ENNReal.ofReal r) ^ s ≤ μ (closedBall x r)) :
    Measure.hausdorffMeasure s E < ⊤ := by
  classical
  let δ : ℕ → ℝ := fun n ↦ (1 / 2 : ℝ) ^ n
  have hδ : ∀ n, 0 < δ n := fun n ↦ pow_pos (by norm_num) n
  have hex : ∀ n : ℕ, ∃ (T : Set ℝ) (r : ℝ → ℝ), T.Countable ∧ T ⊆ E ∧
      (∀ x ∈ T, r x ∈ Ioo 0 (min ε (δ n))) ∧
      (E ⊆ ⋃ x ∈ T, closedBall x (r x)) ∧
      (∑' x : T, μ (closedBall x (r x))) ≤ μ E + 1 := by
    intro n
    apply Besicovitch.exists_closedBall_covering_tsum_measure_le μ one_ne_zero
      (fun _ ↦ Ioo 0 (min ε (δ n))) E
    intro x _ a ha
    have hp : 0 < min (min ε (δ n)) a := lt_min (lt_min hε (hδ n)) ha
    refine ⟨min (min ε (δ n)) a / 2, ?_⟩
    constructor <;> constructor
    · positivity
    · exact (half_lt_self hp).trans_le (min_le_left _ _)
    · positivity
    · exact (half_lt_self hp).trans_le (min_le_right _ _)
  choose T r hT hTE hr hcover hsum using hex
  have hcount (n : ℕ) : Countable (T n) := (hT n).to_subtype
  let C : ℝ≥0∞ := (2 : ℝ≥0∞) ^ s * (μ E + 1)
  have hcost : ∀ n : ℕ, (∑' x : T n, Metric.ediam (closedBall (x : ℝ) (r n x)) ^ s) ≤ C := by
    intro n
    calc
      (∑' x : T n, Metric.ediam (closedBall (x : ℝ) (r n x)) ^ s) ≤
          ∑' x : T n, (2 : ℝ≥0∞) ^ s * μ (closedBall (x : ℝ) (r n x)) := by
        apply ENNReal.tsum_le_tsum
        intro x
        calc
          Metric.ediam (closedBall (x : ℝ) (r n x)) ^ s ≤ (2 * ENNReal.ofReal (r n x)) ^ s :=
            ENNReal.rpow_le_rpow (ediam_closedBall_le_two_mul x (r n x)) hs
          _ = (2 : ℝ≥0∞) ^ s * (ENNReal.ofReal (r n x)) ^ s := ENNReal.mul_rpow_of_nonneg _ _ hs
          _ ≤ _ := mul_le_mul le_rfl
            (hball x (hTE n x.property) _ (hr n x x.property).1
              ((hr n x x.property).2.le.trans (min_le_left _ _))) bot_le bot_le
      _ = (2 : ℝ≥0∞) ^ s * ∑' x : T n, μ (closedBall (x : ℝ) (r n x)) := ENNReal.tsum_mul_left
      _ ≤ C := mul_le_mul le_rfl (hsum n) bot_le bot_le
  have hlim : Tendsto (fun n ↦ 2 * ENNReal.ofReal (δ n)) atTop (𝓝 0) := by
    have hh := ENNReal.continuous_ofReal.tendsto 0 |>.comp
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
    simpa only [ENNReal.ofReal_zero, mul_zero, Function.comp_def] using ENNReal.Tendsto.const_mul (a := (2 : ℝ≥0∞)) hh (Or.inr (by finiteness))
  have hH := Measure.hausdorffMeasure_le_liminf_tsum s E
    (fun n ↦ 2 * ENNReal.ofReal (δ n)) hlim
    (fun n (x : T n) ↦ closedBall (x : ℝ) (r n x))
    (Eventually.of_forall (fun n x ↦ (ediam_closedBall_le_two_mul x (r n x)).trans
      (mul_le_mul le_rfl (ENNReal.ofReal_le_ofReal
        ((hr n x x.property).2.le.trans (min_le_right _ _))) bot_le bot_le)))
    (Eventually.of_forall (fun n ↦ by simpa only [iUnion_subtype] using hcover n))
  apply (hH.trans (liminf_le_of_frequently_le' (Frequently.of_forall hcost))).trans_lt
  dsimp [C]
  finiteness

end ExactOverlaps
