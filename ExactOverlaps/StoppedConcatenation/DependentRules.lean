/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.SequentialRules

/-! A rule chosen using observed stopping-time information is still a genuine bounded stopping time. -/

@[expose] public section

open MeasureTheory

namespace ExactOverlaps.StoppedConcatenation.BoundedStoppingRule

variable {ι α : Type*} [MeasurableSpace ι] [MeasurableSpace α]
  [Countable α] [MeasurableSingletonClass α]

omit [Countable α] in
theorem measurable_observation_time_eq (T : BoundedStoppingRule ι)
    (F : (ℕ → ι) → α) (hF : Measurable[T.adapted.measurableSpace] F) (a : α) (n : ℕ) :
    MeasurableSet[incrementFiltration (ι := ι) n] ({ω | F ω = a} ∩ {ω | T.time ω = n}) := by
  have h := (T.adapted.measurableSet_inter_eq_iff (F ⁻¹' {a}) n).1
    ((hF (measurableSet_singleton a)).inter (T.adapted.measurableSet_eq' n))
  change MeasurableSet[incrementFiltration (ι := ι) n] (F ⁻¹' {a} ∩ {ω | T.time ω = n})
  simpa using h

theorem adapted_dependent_sequential (T : BoundedStoppingRule ι)
    (F : (ℕ → ι) → α) (hF : Measurable[T.adapted.measurableSpace] F)
    (U : α → BoundedStoppingRule ι) : IsStoppingTime incrementFiltration
    (fun ω ↦ ((T.time ω + (U (F ω)).time (T.suffix ω) : ℕ) : WithTop ℕ)) := by
  intro n
  suffices hm : MeasurableSet[incrementFiltration (ι := ι) n]
      {ω | T.time ω + (U (F ω)).time (T.suffix ω) ≤ n} by
    convert hm using 1
    ext ω
    change (((T.time ω + (U (F ω)).time (T.suffix ω) : ℕ) : WithTop ℕ) ≤ (n : WithTop ℕ)) ↔ _
    exact_mod_cast (Iff.rfl : T.time ω + (U (F ω)).time (T.suffix ω) ≤ n ↔
      T.time ω + (U (F ω)).time (T.suffix ω) ≤ n)
  have he : {ω | T.time ω + (U (F ω)).time (T.suffix ω) ≤ n} =
      ⋃ k : Fin (n + 1), ⋃ a : α, ({ω | F ω = a} ∩ {ω | T.time ω = k}) ∩
        (Bernoulli.shift^[(k : ℕ)]) ⁻¹' {ω | (U a).time ω ≤ n - k} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · intro h
      refine ⟨⟨T.time ω, by omega⟩, F ω, ⟨rfl, rfl⟩, ?_⟩
      change (U (F ω)).time (T.suffix ω) ≤ n - T.time ω
      omega
    · rintro ⟨k, a, ⟨ha, hk⟩, hU⟩
      have hs : T.suffix ω = Bernoulli.shift^[(k : ℕ)] ω := by simp only [suffix, hk]
      rw [ha, hs, hk]
      omega
  rw [he]
  apply MeasurableSet.iUnion
  intro k
  apply MeasurableSet.iUnion
  intro a
  have hk : (k : ℕ) ≤ n := by omega
  have hT := (incrementFiltration (ι := ι)).mono hk _ (T.measurable_observation_time_eq F hF a k)
  have hU := (measurable_shift_at (ι := ι) (n - k) k) ((U a).measurableSet_time_le (n - k))
  rw [Nat.sub_add_cancel hk] at hU
  exact hT.inter hU

def andThenChoice (T : BoundedStoppingRule ι)
    (F : (ℕ → ι) → α) (hF : Measurable[T.adapted.measurableSpace] F)
    (U : α → BoundedStoppingRule ι) (N : ℕ) (hN : ∀ a, (U a).horizon ≤ N) :
    BoundedStoppingRule ι where
  time := fun ω ↦ T.time ω + (U (F ω)).time (T.suffix ω)
  horizon := T.horizon + N
  bounded := fun ω ↦ Nat.add_le_add (T.bounded ω) ((U (F ω)).bounded (T.suffix ω) |>.trans (hN _))
  adapted := T.adapted_dependent_sequential F hF U

theorem suffix_andThenChoice (T : BoundedStoppingRule ι)
    (F : (ℕ → ι) → α) (hF : Measurable[T.adapted.measurableSpace] F)
    (U : α → BoundedStoppingRule ι) (N : ℕ) (hN : ∀ a, (U a).horizon ≤ N) (ω : ℕ → ι) :
    (T.andThenChoice F hF U N hN).suffix ω = (U (F ω)).suffix (T.suffix ω) := by
  change Bernoulli.shift^[T.time ω + (U (F ω)).time (T.suffix ω)] ω =
    Bernoulli.shift^[(U (F ω)).time (T.suffix ω)] (Bernoulli.shift^[T.time ω] ω)
  rw [Nat.add_comm, Function.iterate_add_apply]

end ExactOverlaps.StoppedConcatenation.BoundedStoppingRule
