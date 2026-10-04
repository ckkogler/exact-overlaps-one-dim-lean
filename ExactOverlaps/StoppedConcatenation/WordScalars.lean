/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.SequentialWordLaw
public import ExactOverlaps.StoppedConcatenation.MinimumRatio
public import ExactOverlaps.SelfSimilar.WordBounds

/-! Exact signed ratio and translation formulas for variable-length words. -/

@[expose] public section

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι]

noncomputable def totalWordRatio (S : System ι) (w : Σ n : ℕ, Word ι n) : ℝ :=
  S.wordRatio w.1 w.2

noncomputable def totalWordTranslation (S : System ι) (w : Σ n : ℕ, Word ι n) : ℝ :=
  S.wordTranslation w.1 w.2

theorem totalWordRatio_ne_zero (S : System ι) (w : Σ n : ℕ, Word ι n) :
    S.totalWordRatio w ≠ 0 := S.wordRatio_ne_zero w.1 w.2

theorem abs_totalWordRatio_le_one (S : System ι) (w : Σ n : ℕ, Word ι n) :
    |S.totalWordRatio w| ≤ 1 := by
  simpa only [one_pow, totalWordRatio] using S.abs_wordRatio_le_pow (by norm_num : (0 : ℝ) ≤ 1)
    (fun i ↦ (S.contracting i).le) w.1 w.2

theorem totalWordRatio_concatenate (S : System ι) (w v : Σ n : ℕ, Word ι n) :
    S.totalWordRatio (Word.concatenate w v) = S.totalWordRatio w * S.totalWordRatio v := by
  change (S.wordMap (v.1 + w.1) (Word.append w.1 v.1 w.2 v.2)).ratio = _
  rw [S.wordMap_append]
  rfl

theorem totalWordTranslation_concatenate (S : System ι) (w v : Σ n : ℕ, Word ι n) :
    S.totalWordTranslation (Word.concatenate w v) =
      S.totalWordTranslation w + S.totalWordRatio w * S.totalWordTranslation v := by
  change (S.wordMap (v.1 + w.1) (Word.append w.1 v.1 w.2 v.2)).shift = _
  rw [S.wordMap_append]
  exact add_comm _ _

theorem rhoMin_pow_le_abs_wordRatio (S : System ι) (n : ℕ) (w : Word ι n) :
    S.rhoMin ^ n ≤ |S.wordRatio n w| := by
  induction n with
  | zero => change 1 ≤ |(1 : ℝ)|; norm_num
  | succ n ih =>
    rw [wordRatio_succ, abs_mul, pow_succ']
    exact mul_le_mul (S.rhoMin_le w.1) (ih w.2) (pow_nonneg S.rhoMin_pos.le n) (abs_nonneg _)

theorem rhoMin_horizon_le_abs_stoppedWordRatio [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (S : System ι) (T : StoppedConcatenation.BoundedStoppingRule ι) (ω : ℕ → ι) :
    S.rhoMin ^ T.horizon ≤ |S.totalWordRatio (T.stoppedWord ω)| := by
  calc
    S.rhoMin ^ T.horizon ≤ S.rhoMin ^ T.time ω :=
      pow_le_pow_of_le_one S.rhoMin_pos.le S.rhoMin_lt_one.le (T.bounded ω)
    _ ≤ _ := S.rhoMin_pow_le_abs_wordRatio _ _

end ExactOverlaps.SelfSimilar.System
