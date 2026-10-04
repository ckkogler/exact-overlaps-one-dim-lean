module

public import ExactOverlaps.SelfSimilar.AttractorCylinders
public import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
The standard Hausdorff upper bound for the actual attractor. The affine
cylinder cover has uniformly vanishing mesh and bounded total s-cost at
the Moran root. The proof also covers s = 0 and singleton attractors.
-/

@[expose] public section

open Set Metric MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι]

theorem hausdorffMeasure_attractor_ne_top (S : System ι) {s : ℝ} (hs : 0 ≤ s)
    (hpressure : S.pressure s = 1) : Measure.hausdorffMeasure s S.attractor ≠ ⊤ := by
  classical
  obtain ⟨c, _, hc, hc1, _, hmax, _⟩ := S.exists_uniform_bounds
  obtain ⟨D, hD, hdist⟩ := S.exists_attractor_dist_bound
  let t : (n : ℕ) → Word ι n → Set ℝ := fun n w ↦ (S.wordMap n w) '' S.attractor
  let r : ℕ → ℝ≥0∞ := fun n ↦ ENNReal.ofReal (c ^ n * D)
  have hr : Tendsto r atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hc.le hc1).mul_const D
    rw [zero_mul] at h
    simpa only [zero_mul, ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.tendsto 0 |>.comp h
  have hdiam (n : ℕ) (w : Word ι n) : ediam (t n w) ≤ r n := by
    exact (S.ediam_word_image_le hdist n w).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (S.abs_wordRatio_le_pow hc.le hmax n w) hD))
  have hcost (n : ℕ) : (∑ w : Word ι n, ediam (t n w) ^ s) ≤ (ENNReal.ofReal D) ^ s := by
    calc
      _ ≤ ∑ w : Word ι n, (ENNReal.ofReal (|S.wordRatio n w| * D)) ^ s :=
        Finset.sum_le_sum (fun w _ ↦ ENNReal.rpow_le_rpow (S.ediam_word_image_le hdist n w) hs)
      _ = (∑ w : Word ι n, (ENNReal.ofReal |S.wordRatio n w|) ^ s) * (ENNReal.ofReal D) ^ s := by
        simp only [ENNReal.ofReal_mul (abs_nonneg _), ENNReal.mul_rpow_of_nonneg _ _ hs,
          Finset.sum_mul]
      _ = _ := by rw [S.sum_wordRatio_ennreal_rpow hs hpressure, one_mul]
  have hH := Measure.hausdorffMeasure_le_liminf_sum s S.attractor r hr t
    (Eventually.of_forall hdiam) (Eventually.of_forall S.attractor_subset_word_union)
  apply ne_top_of_le_ne_top _ (hH.trans (liminf_le_of_frequently_le' (Frequently.of_forall hcost)))
  exact ENNReal.rpow_ne_top_of_nonneg hs ENNReal.ofReal_ne_top

theorem dimH_attractor_le_similarity_root (S : System ι) {s : ℝ} (hs : 0 ≤ s)
    (hpressure : S.pressure s = 1) : dimH S.attractor ≤ ENNReal.ofReal s := by
  have h := dimH_le_of_hausdorffMeasure_ne_top (d := NNReal.mk s hs)
    (S.hausdorffMeasure_attractor_ne_top hs hpressure)
  simpa only [ENNReal.ofReal_eq_coe_nnreal hs] using h

theorem dimH_attractor_le_one (S : System ι) : dimH S.attractor ≤ 1 := by
  simpa only [Real.dimH_univ] using (dimH_mono (subset_univ S.attractor))

theorem dimH_attractor_le_min (S : System ι) {s : ℝ} (hs : 0 ≤ s)
    (hpressure : S.pressure s = 1) : dimH S.attractor ≤ ENNReal.ofReal (min 1 s) := by
  rw [ENNReal.ofReal_min, ENNReal.ofReal_one]
  exact le_min S.dimH_attractor_le_one (S.dimH_attractor_le_similarity_root hs hpressure)

end ExactOverlaps.SelfSimilar.System
