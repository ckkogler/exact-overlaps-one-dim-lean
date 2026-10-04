/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.MinimumRatio
public import ExactOverlaps.StoppedConcatenation.ThresholdWordLaw

/-! Uniformly bounded ratio thresholds after an already observed contraction. -/

@[expose] public section

open MeasureTheory

namespace ExactOverlaps.StoppedConcatenation.BoundedStoppingRule

variable {ι : Type*} [MeasurableSpace ι]

def withBound (T : BoundedStoppingRule ι) (N : ℕ) (hN : ∀ ω, T.time ω ≤ N) :
    BoundedStoppingRule ι where
  time := T.time
  horizon := N
  bounded := hN
  adapted := T.adapted

end ExactOverlaps.StoppedConcatenation.BoundedStoppingRule

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

noncomputable def adjustedCrossingRule (S : System ι) (r : ℝ) (hr : 0 < r)
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) : StoppedConcatenation.BoundedStoppingRule ι :=
  (S.ratioCrossingRule (r / a) (div_pos hr ha)).withBound
    (S.ratioCrossingRule r hr).horizon (fun ω ↦
      (S.ratioCrossingTime_antitone hr (div_pos hr ha)
        ((le_div_iff₀ ha).2 (mul_le_of_le_one_right hr.le ha1)) ω).trans
          ((S.ratioCrossingRule r hr).bounded ω))

theorem adjustedCrossingRule_time (S : System ι) (r : ℝ) (hr : 0 < r)
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (ω : ℕ → ι) :
    (S.adjustedCrossingRule r hr a ha ha1).time ω =
      S.ratioCrossingTime (r / a) (div_pos hr ha) ω := rfl

theorem adjustedCrossingRule_upper (S : System ι) (r : ℝ) (hr : 0 < r)
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (ω : ℕ → ι) :
    a * |S.prefixRatio ((S.adjustedCrossingRule r hr a ha ha1).time ω) ω| ≤ r := by
  have h := S.ratioCrossingTime_upper (r / a) (div_pos hr ha) ω
  change a * |S.prefixRatio (S.ratioCrossingTime (r / a) (div_pos hr ha) ω) ω| ≤ r
  simpa only [mul_comm] using (le_div_iff₀ ha).mp h

theorem adjustedCrossingRule_lower (S : System ι) (r : ℝ) (hr : 0 < r)
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (hra : r ≤ a) (ω : ℕ → ι) :
    S.rhoMin * r < a * |S.prefixRatio ((S.adjustedCrossingRule r hr a ha ha1).time ω) ω| := by
  have h := S.ratioCrossingTime_lower (r / a) (div_pos hr ha)
    ((div_le_one ha).2 hra) S.rhoMin_pos S.rhoMin_lt_one S.rhoMin_le ω
  change S.rhoMin * r < a * |S.prefixRatio (S.ratioCrossingTime (r / a) (div_pos hr ha) ω) ω|
  have hh := mul_lt_mul_of_pos_left h ha
  convert hh using 1
  field_simp

end ExactOverlaps.SelfSimilar.System
