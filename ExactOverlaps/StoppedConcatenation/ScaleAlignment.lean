/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.HeadContinuation
public import ExactOverlaps.StoppedConcatenation.ThresholdWordLaw

/-! Exact relative-scale inequalities at the first ratio crossing, with signed ratios retained. -/

@[expose] public section

namespace ExactOverlaps.StoppedConcatenation

open SelfSimilar

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem crossing_scale_window (S : System ι) {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hrs : r ≤ s) (g : ((S.ratioCrossingRule (r / s) (div_pos hr hs)).stoppedWordLaw S.alphabetLaw).support) :
    s ≤ r / |S.totalWordRatio g| ∧ r / |S.totalWordRatio g| < s / S.rhoMin := by
  have hg := S.ratioCrossingWordLaw_bounds (r / s) (div_pos hr hs) ((div_le_one hs).2 hrs) g
  change S.rhoMin * (r / s) < |S.totalWordRatio g| ∧ |S.totalWordRatio g| ≤ r / s at hg
  have hp := abs_pos.mpr (S.totalWordRatio_ne_zero g)
  constructor
  · apply (le_div_iff₀ hp).2
    have h := (le_div_iff₀ hs).mp hg.2
    nlinarith
  · apply (div_lt_div_iff₀ hp S.rhoMin_pos).2
    have h := mul_lt_mul_of_pos_right hg.1 hs
    have he : S.rhoMin * (r / s) * s = r * S.rhoMin := by field_simp
    rw [he] at h
    nlinarith

theorem crossing_power_window (S : System ι) {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hrs : r ≤ s) (g : ((S.ratioCrossingRule (r / s) (div_pos hr hs)).stoppedWordLaw S.alphabetLaw).support) :
    S.rhoMin ^ 2 ≤ s ^ 2 / (r / |S.totalWordRatio g|) ^ 2 := by
  obtain ⟨_, h⟩ := crossing_scale_window S hr hs hrs g
  have ht := div_pos hr (abs_pos.mpr (S.totalWordRatio_ne_zero g))
  have hmul : (r / |S.totalWordRatio g|) * S.rhoMin < s := (lt_div_iff₀ S.rhoMin_pos).mp h
  apply (le_div_iff₀ (sq_pos_of_pos ht)).2
  nlinarith [mul_self_le_mul_self (mul_pos ht S.rhoMin_pos).le hmul.le]

theorem head_next_scale_le (S : System ι) (T : BoundedStoppingRule ι)
    {r s t : ℝ} (hr : 0 < r) (hs : 0 < s) (hrs : r ≤ s)
    (hsep : ∀ w ∈ (T.stoppedWordLaw S.alphabetLaw).support,
      s ≤ S.rhoMin * t * |S.totalWordRatio w|)
    (b : (headLabelLaw S (S.ratioCrossingRule (r / s) (div_pos hr hs)) T).support) :
    0 < r / (|S.totalWordRatio b.val.1| * |b.val.2|) ∧
      r / (|S.totalWordRatio b.val.1| * |b.val.2|) ≤ t := by
  obtain ⟨hg, w, hw, hRw⟩ := headLabelLaw_support S _ T b
  have hG := abs_pos.mpr (S.totalWordRatio_ne_zero b.val.1)
  have hC : 0 < |b.val.2| := hRw ▸ abs_pos.mpr (S.totalWordRatio_ne_zero w)
  have hwindow := (crossing_scale_window S hr hs hrs ⟨b.val.1, hg⟩).2
  have hsep' : s ≤ S.rhoMin * t * |b.val.2| := hRw ▸ hsep w hw
  constructor
  · exact div_pos hr (mul_pos hG hC)
  · apply (div_le_iff₀ (mul_pos hG hC)).2
    have h₁ : (r / |S.totalWordRatio b.val.1|) * S.rhoMin < s :=
      (lt_div_iff₀ S.rhoMin_pos).mp hwindow
    have h₂ : r / |S.totalWordRatio b.val.1| ≤ t * |b.val.2| := by
      nlinarith [S.rhoMin_pos]
    have h₃ := (div_le_iff₀ hG).mp h₂
    nlinarith

end ExactOverlaps.StoppedConcatenation
