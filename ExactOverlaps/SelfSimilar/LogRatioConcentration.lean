module

public import ExactOverlaps.SelfSimilar.LogRatioMoments
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
A finite-word weak law of large numbers for logarithmic contraction. The
exceptional mass is bounded explicitly by the one-letter variance divided
by n ε². In particular, no positivity assumption on the signed multipliers
or on every individual branch weight is needed.
-/

@[expose] public section

open Filter
open scoped BigOperators Classical Topology

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι]

/-- Probability that the word's average log-contraction deviates by at least ε. -/
noncomputable def logRatioDeviationProbability (S : System ι) (ε : ℝ) (n : ℕ) : ℝ :=
  ∑ w ∈ Finset.univ.filter (fun w ↦ (n : ℝ) * ε ≤ |S.centeredWordLogRatio n w|),
    S.wordProbability n w

theorem logRatioDeviationProbability_nonneg (S : System ι) (ε : ℝ) (n : ℕ) :
    0 ≤ S.logRatioDeviationProbability ε n :=
  Finset.sum_nonneg fun w _ ↦ S.wordProbability_nonneg n w

theorem logRatioDeviationProbability_le_one (S : System ι) (ε : ℝ) (n : ℕ) :
    S.logRatioDeviationProbability ε n ≤ 1 := by
  rw [← S.wordProbability_sum n]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun w _ _ ↦ S.wordProbability_nonneg n w)

theorem centeredWordLogRatio_abs_eq (S : System ι) {n : ℕ} (hn : 0 < n) (w : Word ι n) :
    |S.centeredWordLogRatio n w| =
      (n : ℝ) * |S.wordLogRatio n w / n - S.lyapunov| := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have he : S.centeredWordLogRatio n w =
      (n : ℝ) * (S.wordLogRatio n w / n - S.lyapunov) := by
    dsimp [centeredWordLogRatio]
    field_simp
  rw [he, abs_mul, abs_of_pos hn']

theorem logRatio_deviation_iff (S : System ι) {n : ℕ} (hn : 0 < n)
    (w : Word ι n) (ε : ℝ) :
    (n : ℝ) * ε ≤ |S.centeredWordLogRatio n w| ↔
      ε ≤ |S.wordLogRatio n w / n - S.lyapunov| := by
  rw [S.centeredWordLogRatio_abs_eq hn]
  exact mul_le_mul_iff_right₀ (by exact_mod_cast hn : (0 : ℝ) < n)

/-- Chebyshev estimate, proved directly for the actual finite product weights. -/
theorem logRatioDeviationProbability_le (S : System ι) {ε : ℝ} (hε : 0 < ε)
    {n : ℕ} (hn : 0 < n) :
    S.logRatioDeviationProbability ε n ≤ S.logRatioVariance / ((n : ℝ) * ε ^ 2) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let B := Finset.univ.filter (fun w : Word ι n ↦
    (n : ℝ) * ε ≤ |S.centeredWordLogRatio n w|)
  have hbound : ((n : ℝ) * ε) ^ 2 * S.logRatioDeviationProbability ε n ≤
      (n : ℝ) * S.logRatioVariance := by
    calc
      ((n : ℝ) * ε) ^ 2 * S.logRatioDeviationProbability ε n =
          ∑ w ∈ B, S.wordProbability n w * ((n : ℝ) * ε) ^ 2 := by
        rw [logRatioDeviationProbability, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro w _
        ring
      _ ≤ ∑ w ∈ B, S.wordProbability n w * (S.centeredWordLogRatio n w) ^ 2 := by
        apply Finset.sum_le_sum
        intro w hw
        apply mul_le_mul_of_nonneg_left _ (S.wordProbability_nonneg n w)
        have hbad := (Finset.mem_filter.mp hw).2
        have hh := mul_self_le_mul_self (mul_nonneg hn'.le hε.le) hbad
        simpa only [← sq, sq_abs] using hh
      _ ≤ ∑ w, S.wordProbability n w * (S.centeredWordLogRatio n w) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun w _ _ ↦ mul_nonneg (S.wordProbability_nonneg n w) (sq_nonneg _))
      _ = (n : ℝ) * S.logRatioVariance := S.centeredWordLogRatio_secondMoment n
  apply (le_div_iff₀ (mul_pos hn' (sq_pos_of_pos hε))).mpr
  apply (mul_le_mul_iff_right₀ hn').mp
  calc
    (n : ℝ) * (S.logRatioDeviationProbability ε n * ((n : ℝ) * ε ^ 2)) =
        ((n : ℝ) * ε) ^ 2 * S.logRatioDeviationProbability ε n := by ring
    _ ≤ (n : ℝ) * S.logRatioVariance := hbound

theorem logRatioDeviationProbability_tendsto_zero (S : System ι)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (S.logRatioDeviationProbability ε) atTop (𝓝 0) := by
  have hupper : Tendsto (fun n : ℕ ↦ S.logRatioVariance / ((n : ℝ) * ε ^ 2))
      atTop (𝓝 0) := by
    have h := tendsto_const_div_atTop_nhds_zero_nat (S.logRatioVariance / ε ^ 2)
    convert h using 1
    ext n
    ring
  apply squeeze_zero'
    (Eventually.of_forall fun n ↦ S.logRatioDeviationProbability_nonneg ε n) _ hupper
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact S.logRatioDeviationProbability_le hε hn

end ExactOverlaps.SelfSimilar.System
