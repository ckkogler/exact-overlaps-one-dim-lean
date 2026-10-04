/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.EmbeddingWitness

/-! The terminal block end and its observation are unchanged by identical start times. -/

@[expose] public section

namespace ExactOverlaps.StoppedConcatenation.BoundedStoppingRule

variable {ι : Type*} [MeasurableSpace ι]

theorem suffix_eq_of_time_eq (A B : BoundedStoppingRule ι)
    (h : ∀ ω, A.time ω = B.time ω) (ω : ℕ → ι) : A.suffix ω = B.suffix ω := by
  simp only [suffix, h ω]

theorem andThen_time_eq_of_time_eq (A B T : BoundedStoppingRule ι)
    (h : ∀ ω, A.time ω = B.time ω) (ω : ℕ → ι) :
    (A.andThen T).time ω = (B.andThen T).time ω := by
  change A.time ω + T.time (A.suffix ω) = B.time ω + T.time (B.suffix ω)
  rw [h ω, A.suffix_eq_of_time_eq B h ω]

end ExactOverlaps.StoppedConcatenation.BoundedStoppingRule
