module

public import ExactOverlaps.SelfSimilar.Words

/-!
Exact first and second moments of the logarithm of the signed word multiplier.
The product law is finite, so these identities follow directly by induction
on word length and do not require a symbolic-dynamics ergodic theorem.
-/

@[expose] public section

open scoped ENNReal BigOperators

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι]

noncomputable def wordProbability (S : System ι) (n : ℕ) (w : Word ι n) : ℝ :=
  (S.wordWeight n w).toReal

theorem wordProbability_nonneg (S : System ι) (n : ℕ) (w : Word ι n) :
    0 ≤ S.wordProbability n w := ENNReal.toReal_nonneg

@[simp] theorem wordProbability_zero (S : System ι) (w : Word ι 0) :
    S.wordProbability 0 w = 1 := by simp [wordProbability, wordWeight]

@[simp] theorem wordProbability_succ (S : System ι) (n : ℕ) (w : Word ι (n + 1)) :
    S.wordProbability (n + 1) w = (S.weight w.1 : ℝ) * S.wordProbability n w.2 := by
  simp [wordProbability, wordWeight, ENNReal.toReal_mul]

theorem wordProbability_sum (S : System ι) (n : ℕ) : ∑ w, S.wordProbability n w = 1 := by
  induction n with
  | zero => change (∑ _w : PUnit, (1 : ℝ)) = 1; simp
  | succ n ih =>
    simp_rw [wordProbability_succ]
    change (∑ w : ι × Word ι n, (S.weight w.1 : ℝ) * S.wordProbability n w.2) = 1
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, ih, mul_one]
    exact S.weight_sum_real

/-- Logarithmic absolute contraction, with reflection retained in wordRatio. -/
noncomputable def wordLogRatio (S : System ι) (n : ℕ) (w : Word ι n) : ℝ :=
  Real.log |S.wordRatio n w|

@[simp] theorem wordLogRatio_zero (S : System ι) (w : Word ι 0) :
    S.wordLogRatio 0 w = 0 := by
  simp [wordLogRatio, wordRatio, wordMap, RealSimilarity.identity]

theorem wordLogRatio_succ (S : System ι) (n : ℕ) (w : Word ι (n + 1)) :
    S.wordLogRatio (n + 1) w = Real.log |(S.map w.1).ratio| + S.wordLogRatio n w.2 := by
  rw [wordLogRatio, wordRatio_succ, abs_mul,
    Real.log_mul (abs_ne_zero.mpr (S.map w.1).ratio_ne_zero)
      (abs_ne_zero.mpr (S.wordRatio_ne_zero n w.2))]
  rfl

theorem wordLogRatio_mean (S : System ι) (n : ℕ) :
    ∑ w, S.wordProbability n w * S.wordLogRatio n w = (n : ℝ) * S.lyapunov := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp_rw [wordProbability_succ, wordLogRatio_succ]
    change (∑ w : ι × Word ι n,
      (S.weight w.1 : ℝ) * S.wordProbability n w.2 *
        (Real.log |(S.map w.1).ratio| + S.wordLogRatio n w.2)) = _
    rw [Fintype.sum_prod_type]
    have hinner (i : ι) :
        ∑ w : Word ι n, (S.weight i : ℝ) * S.wordProbability n w *
            (Real.log |(S.map i).ratio| + S.wordLogRatio n w) =
          (S.weight i : ℝ) * Real.log |(S.map i).ratio| +
          (S.weight i : ℝ) * ((n : ℝ) * S.lyapunov) := by
      calc
        ∑ w : Word ι n, (S.weight i : ℝ) * S.wordProbability n w *
            (Real.log |(S.map i).ratio| + S.wordLogRatio n w) =
          ∑ w : Word ι n, (((S.weight i : ℝ) * Real.log |(S.map i).ratio|) *
            S.wordProbability n w + (S.weight i : ℝ) *
              (S.wordProbability n w * S.wordLogRatio n w)) := by
                apply Finset.sum_congr rfl
                intro w _
                ring
        _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          S.wordProbability_sum n, ih, mul_one]
    simp_rw [hinner]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, S.weight_sum_real, one_mul]
    change S.lyapunov + (n : ℝ) * S.lyapunov = _
    push_cast
    ring

noncomputable def centeredWordLogRatio (S : System ι) (n : ℕ) (w : Word ι n) : ℝ :=
  S.wordLogRatio n w - (n : ℝ) * S.lyapunov

theorem centeredWordLogRatio_succ (S : System ι) (n : ℕ) (w : Word ι (n + 1)) :
    S.centeredWordLogRatio (n + 1) w =
      (Real.log |(S.map w.1).ratio| - S.lyapunov) + S.centeredWordLogRatio n w.2 := by
  simp only [centeredWordLogRatio, wordLogRatio_succ, Nat.cast_add, Nat.cast_one]
  ring

theorem centeredWordLogRatio_mean (S : System ι) (n : ℕ) :
    ∑ w, S.wordProbability n w * S.centeredWordLogRatio n w = 0 := by
  simp only [centeredWordLogRatio, mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul, S.wordProbability_sum, S.wordLogRatio_mean, one_mul, sub_self]

/-- Variance of one logarithmic absolute contraction. -/
noncomputable def logRatioVariance (S : System ι) : ℝ :=
  ∑ i, (S.weight i : ℝ) * (Real.log |(S.map i).ratio| - S.lyapunov) ^ 2

theorem logRatioVariance_nonneg (S : System ι) : 0 ≤ S.logRatioVariance :=
  Finset.sum_nonneg fun i _ ↦ mul_nonneg (S.weight i).coe_nonneg (sq_nonneg _)

theorem centeredWordLogRatio_secondMoment (S : System ι) (n : ℕ) :
    ∑ w, S.wordProbability n w * (S.centeredWordLogRatio n w) ^ 2 =
      (n : ℝ) * S.logRatioVariance := by
  induction n with
  | zero =>
    simp [centeredWordLogRatio]
  | succ n ih =>
    simp_rw [wordProbability_succ, centeredWordLogRatio_succ]
    change (∑ w : ι × Word ι n,
      (S.weight w.1 : ℝ) * S.wordProbability n w.2 *
        ((Real.log |(S.map w.1).ratio| - S.lyapunov) + S.centeredWordLogRatio n w.2) ^ 2) = _
    rw [Fintype.sum_prod_type]
    have hinner (i : ι) :
        ∑ w : Word ι n, (S.weight i : ℝ) * S.wordProbability n w *
            ((Real.log |(S.map i).ratio| - S.lyapunov) + S.centeredWordLogRatio n w) ^ 2 =
          (S.weight i : ℝ) * (Real.log |(S.map i).ratio| - S.lyapunov) ^ 2 +
          (S.weight i : ℝ) * ((n : ℝ) * S.logRatioVariance) := by
      calc
        ∑ w : Word ι n, (S.weight i : ℝ) * S.wordProbability n w *
            ((Real.log |(S.map i).ratio| - S.lyapunov) + S.centeredWordLogRatio n w) ^ 2 =
          ∑ w : Word ι n,
            (((S.weight i : ℝ) * (Real.log |(S.map i).ratio| - S.lyapunov) ^ 2) *
              S.wordProbability n w +
            (2 * (S.weight i : ℝ) * (Real.log |(S.map i).ratio| - S.lyapunov)) *
              (S.wordProbability n w * S.centeredWordLogRatio n w) +
            (S.weight i : ℝ) * (S.wordProbability n w * (S.centeredWordLogRatio n w) ^ 2)) := by
              apply Finset.sum_congr rfl
              intro w _
              ring
        _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
            ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
            S.wordProbability_sum n, S.centeredWordLogRatio_mean n, ih]
          ring
    simp_rw [hinner]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, S.weight_sum_real, one_mul]
    change S.logRatioVariance + (n : ℝ) * S.logRatioVariance = _
    push_cast
    ring

end ExactOverlaps.SelfSimilar.System
