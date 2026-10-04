module

public import ExactOverlaps.SelfSimilar.LyapunovConcentration
public import Mathlib.MeasureTheory.Function.Floor
public import ExactOverlaps.Entropy.ConditionalConcavity

/-!
Integer dyadic levels of signed contraction classes and their law of large
numbers. The rounding error is retained explicitly; the normalized absolute
ratio lies in (1/2, 1].
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace ExactOverlaps.SelfSimilar

/-- Dyadic scale of the absolute value of a signed contraction. -/
noncomputable def ratioLevel (t : ℝ) : ℤ := ⌊-Real.log |t| / Real.log 2⌋

theorem measurable_ratioLevel : Measurable ratioLevel := by
  unfold ratioLevel
  exact Int.measurable_floor.comp (by fun_prop)

theorem ratioLevel_mul_le_one {t : ℝ} (ht : t ≠ 0) :
    (2 : ℝ) ^ ratioLevel t * |t| ≤ 1 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hf := (le_div_iff₀ hlog).mp (Int.floor_le (-Real.log |t| / Real.log 2))
  apply (Real.log_le_log_iff
    (mul_pos (zpow_pos (by norm_num) _) (abs_pos.mpr ht)) zero_lt_one).mp
  rw [Real.log_mul (zpow_pos (by norm_num : (0 : ℝ) < 2) _).ne'
    (abs_pos.mpr ht).ne', Real.log_zpow, Real.log_one]
  dsimp [ratioLevel]
  linarith

theorem half_lt_ratioLevel_mul {t : ℝ} (ht : t ≠ 0) :
    (1 : ℝ) / 2 < (2 : ℝ) ^ ratioLevel t * |t| := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hf := (div_lt_iff₀ hlog).mp (Int.lt_floor_add_one (-Real.log |t| / Real.log 2))
  apply (Real.log_lt_log_iff (by norm_num)
    (mul_pos (zpow_pos (by norm_num) _) (abs_pos.mpr ht))).mp
  rw [Real.log_mul (zpow_pos (by norm_num : (0 : ℝ) < 2) _).ne'
    (abs_pos.mpr ht).ne', Real.log_zpow, Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
      (by norm_num : (2 : ℝ) ≠ 0), Real.log_one]
  dsimp [ratioLevel]
  linarith

theorem ratioLevel_rounding_error (t : ℝ) :
    |(ratioLevel t : ℝ) - (-Real.log |t| / Real.log 2)| ≤ 1 := by
  have h₁ := Int.floor_le (-Real.log |t| / Real.log 2)
  have h₂ := Int.lt_floor_add_one (-Real.log |t| / Real.log 2)
  rw [abs_le]
  dsimp [ratioLevel]
  constructor <;> linarith

theorem ratioLevel_deviation_le (t χ : ℝ) (n : ℕ) :
    |(ratioLevel t : ℝ) - (-χ / Real.log 2) * n| ≤
      |Real.log |t| - (n : ℝ) * χ| / Real.log 2 + 1 := by
  have he : -Real.log |t| / Real.log 2 - (-χ / Real.log 2) * n =
      -(Real.log |t| - (n : ℝ) * χ) / Real.log 2 := by ring
  calc
    _ ≤ |(ratioLevel t : ℝ) - (-Real.log |t| / Real.log 2)| +
        |(-Real.log |t| / Real.log 2) - (-χ / Real.log 2) * n| := abs_sub_le _ _ _
    _ ≤ 1 + |Real.log |t| - (n : ℝ) * χ| / Real.log 2 := by
      rw [he, abs_div, abs_neg, abs_of_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
      linarith [ratioLevel_rounding_error t]
    _ = _ := add_comm _ _

namespace System

variable {ι : Type*} [Fintype ι]

/-- Positive mean contraction per letter in dyadic units. -/
noncomputable def dyadicLyapunov (S : System ι) : ℝ := -S.lyapunov / Real.log 2

theorem dyadicLyapunov_pos (S : System ι) : 0 < S.dyadicLyapunov :=
  div_pos (neg_pos.mpr S.lyapunov_neg) (Real.log_pos (by norm_num))

/-- Signed contraction classes whose integer level is outside the typical window. -/
def atypicalRatioLevelSet (S : System ι) (ε : ℝ) (n : ℕ) : Set ℝ :=
  {t | ¬ ((S.dyadicLyapunov - ε) * n ≤ (ratioLevel t : ℝ) ∧
    (ratioLevel t : ℝ) ≤ (S.dyadicLyapunov + ε) * n)}

theorem measurableSet_atypicalRatioLevelSet (S : System ι) (ε : ℝ) (n : ℕ) :
    MeasurableSet (S.atypicalRatioLevelSet ε n) := by
  have hm : Measurable (fun t : ℝ ↦ (ratioLevel t : ℝ)) :=
    (measurable_of_countable (fun z : ℤ ↦ (z : ℝ))).comp measurable_ratioLevel
  exact ((measurableSet_le measurable_const hm).inter
    (measurableSet_le hm measurable_const)).compl

theorem wordRatio_level_typical (S : System ι) {ε : ℝ} {n : ℕ}
    (hn : 2 ≤ ε * (n : ℝ)) (w : Word ι n)
    (hw : |S.centeredWordLogRatio n w| < (n : ℝ) * (ε * Real.log 2 / 2)) :
    (S.dyadicLyapunov - ε) * n ≤ (ratioLevel (S.wordRatio n w) : ℝ) ∧
      (ratioLevel (S.wordRatio n w) : ℝ) ≤ (S.dyadicLyapunov + ε) * n := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb := ratioLevel_deviation_le (S.wordRatio n w) S.lyapunov n
  have hd : |Real.log |S.wordRatio n w| - (n : ℝ) * S.lyapunov| / Real.log 2 <
      ε * n / 2 := by
    apply (div_lt_iff₀ hlog).mpr
    dsimp [centeredWordLogRatio, wordLogRatio] at hw
    nlinarith
  have habs : |(ratioLevel (S.wordRatio n w) : ℝ) - S.dyadicLyapunov * n| ≤ ε * n := by
    dsimp [dyadicLyapunov]
    linarith
  rw [abs_le] at habs
  constructor <;> nlinarith [habs.1, habs.2]

end System
end ExactOverlaps.SelfSimilar
