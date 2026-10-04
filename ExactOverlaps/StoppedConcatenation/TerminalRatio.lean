/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.WordScalars
public import ExactOverlaps.StoppedConcatenation.ThresholdWordLaw

/-! The final block retains its actual ratio; a horizon bound yields the stated relative-scale corollary. -/

@[expose] public section

open MeasureTheory

namespace ExactOverlaps.StoppedConcatenation

open SelfSimilar Entropy

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem stoppedWord_length_le_horizon (T : BoundedStoppingRule ι) (p : PMF ι)
    (w : Σ n : ℕ, Word ι n) (hw : w ∈ (T.stoppedWordLaw p).support) : w.1 ≤ T.horizon := by
  obtain ⟨ω, hT, _⟩ := T.admissible_of_mem_stoppedWordLaw_support p w hw
  exact hT ▸ T.bounded ω

theorem stoppedWord_ratio_ge_horizon (S : System ι) (T : BoundedStoppingRule ι)
    (w : Σ n : ℕ, Word ι n) (hw : w ∈ (T.stoppedWordLaw S.alphabetLaw).support) :
    S.rhoMin ^ T.horizon ≤ |S.totalWordRatio w| := by
  exact (pow_le_pow_of_le_one S.rhoMin_pos.le S.rhoMin_lt_one.le
    (stoppedWord_length_le_horizon T S.alphabetLaw w hw)).trans
      (S.rhoMin_pow_le_abs_wordRatio w.1 w.2)

theorem terminal_ratio_actual_block (S : System ι) (A T : BoundedStoppingRule ι)
    {r s : ℝ} (hA : ∀ a ∈ (A.stoppedWordLaw S.alphabetLaw).support,
      S.rhoMin * r / s < |S.totalWordRatio a|)
    (a : (A.stoppedWordLaw S.alphabetLaw).support)
    (w : (T.stoppedWordLaw S.alphabetLaw).support) :
    S.rhoMin * r * |S.totalWordRatio w| / s <
      |S.totalWordRatio (Word.concatenate a w)| := by
  rw [S.totalWordRatio_concatenate, abs_mul]
  have h := mul_lt_mul_of_pos_right (hA a a.property) (abs_pos.mpr (S.totalWordRatio_ne_zero w))
  simpa only [div_mul_eq_mul_div] using h

theorem terminal_relative_scale_bound (S : System ι) (A T : BoundedStoppingRule ι)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hA : ∀ a ∈ (A.stoppedWordLaw S.alphabetLaw).support,
      S.rhoMin * r / s < |S.totalWordRatio a|) :
    ∀ u ∈ ((A.andThen T).stoppedWordLaw S.alphabetLaw).support,
      r / |S.totalWordRatio u| < s / S.rhoMin ^ (T.horizon + 1) := by
  intro u hu
  rw [A.andThen_stoppedWordLaw T] at hu
  obtain ⟨⟨a, w⟩, haw, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hu
  rw [independentPair_support] at haw
  have h := terminal_ratio_actual_block S A T hA ⟨a, haw.1⟩ ⟨w, haw.2⟩
  have hW := stoppedWord_ratio_ge_horizon S T w haw.2
  have hc : 0 < S.rhoMin * r / s := div_pos (mul_pos S.rhoMin_pos hr) hs
  have hm := mul_le_mul_of_nonneg_left hW hc.le
  have hlow : S.rhoMin ^ (T.horizon + 1) * r / s < |S.totalWordRatio u| := by
    rw [← he, pow_succ]
    change S.rhoMin ^ T.horizon * S.rhoMin * r / s < _
    have h' : S.rhoMin * r / s * |S.totalWordRatio w| <
        |S.totalWordRatio (Word.concatenate a w)| := by simpa only [div_mul_eq_mul_div] using h
    convert hm.trans_lt h' using 1
    ring
  apply (div_lt_div_iff₀ (abs_pos.mpr (S.totalWordRatio_ne_zero u))
    (pow_pos S.rhoMin_pos _)).2
  have hmul := (div_lt_iff₀ hs).mp hlow
  nlinarith

end ExactOverlaps.StoppedConcatenation
