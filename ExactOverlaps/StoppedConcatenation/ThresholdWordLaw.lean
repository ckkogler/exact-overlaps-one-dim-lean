/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.StoppedWordLaw
public import ExactOverlaps.StoppedConcatenation.MinimumRatio

/-! Every positive-mass threshold word obeys the exact strict contraction bounds. -/

@[expose] public section

namespace ExactOverlaps

namespace StoppedConcatenation.BoundedStoppingRule

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem admissible_of_mem_stoppedWordLaw_support (T : BoundedStoppingRule ι) (p : PMF ι)
    (z : Σ n : ℕ, SelfSimilar.Word ι n) (hz : z ∈ (T.stoppedWordLaw p).support) :
    T.Admissible z.1 z.2 := by
  by_contra h
  exact (show T.stoppedWordLaw p z ≠ 0 from hz)
    (T.stoppedWordLaw_apply_of_not_admissible p z.1 z.2 h)

end StoppedConcatenation.BoundedStoppingRule

namespace SelfSimilar.System

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem ratioCrossingWordLaw_bounds (S : System ι) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (z : ((S.ratioCrossingRule r hr).stoppedWordLaw S.alphabetLaw).support) :
    S.rhoMin * r < |S.wordRatio z.val.1 z.val.2| ∧ |S.wordRatio z.val.1 z.val.2| ≤ r := by
  obtain ⟨ω, ht, hw⟩ := (S.ratioCrossingRule r hr).admissible_of_mem_stoppedWordLaw_support
    S.alphabetLaw z z.property
  change S.ratioCrossingTime r hr ω = z.val.1 at ht
  have he : S.wordRatio z.val.1 z.val.2 =
      S.prefixRatio (S.ratioCrossingTime r hr ω) ω := by
    rw [ht, ← S.wordRatio_read, hw]
  rw [he]
  exact ⟨S.ratioCrossingTime_rhoMin_lower r hr hr1 ω, S.ratioCrossingTime_upper r hr ω⟩

end SelfSimilar.System
end ExactOverlaps
