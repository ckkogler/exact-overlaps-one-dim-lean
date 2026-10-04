/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.SequentialWordLaw

/-! Both successive block observations belong to the actual final stopping sigma-algebra. -/

@[expose] public section

open MeasureTheory

namespace ExactOverlaps.StoppedConcatenation.BoundedStoppingRule

variable {ι α : Type*} [MeasurableSpace ι] [MeasurableSpace α]

theorem measurable_at_andThen_left (T U : BoundedStoppingRule ι)
    (F : (ℕ → ι) → α) (hF : Measurable[T.adapted.measurableSpace] F) :
    Measurable[(T.andThen U).adapted.measurableSpace] F := by
  apply hF.mono _ le_rfl
  apply T.adapted.measurableSpace_mono (T.andThen U).adapted
  intro ω
  change (T.time ω : WithTop ℕ) ≤ ((T.time ω + U.time (T.suffix ω) : ℕ) : WithTop ℕ)
  exact_mod_cast Nat.le_add_right (T.time ω) (U.time (T.suffix ω))

theorem measurable_at_andThen_right (T U : BoundedStoppingRule ι)
    (G : (ℕ → ι) → α) (hG : Measurable[U.adapted.measurableSpace] G) :
    Measurable[(T.andThen U).adapted.measurableSpace] (fun ω ↦ G (T.suffix ω)) := by
  intro E hE
  let A (m n : ℕ) : Set (ℕ → ι) :=
    {ω | T.time ω = m} ∩ (Bernoulli.shift^[m]) ⁻¹' (G ⁻¹' E ∩ {ω | U.time ω = n})
  have he : (fun ω ↦ G (T.suffix ω)) ⁻¹' E = ⋃ m : ℕ, ⋃ n : ℕ, A m n := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, A, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨T.time ω, U.time (T.suffix ω), rfl, h, rfl⟩
    · rintro ⟨m, n, hm, h, _⟩
      simpa only [suffix, hm] using h
  rw [he]
  apply MeasurableSet.iUnion
  intro m
  apply MeasurableSet.iUnion
  intro n
  have hA : MeasurableSet[incrementFiltration (ι := ι) (n + m)] (A m n) := by
    have hU := (U.adapted.measurableSet_inter_eq_iff (G ⁻¹' E) n).1
      ((hG hE).inter (U.adapted.measurableSet_eq' n))
    have hU' : MeasurableSet[incrementFiltration (ι := ι) n]
        (G ⁻¹' E ∩ {ω | U.time ω = n}) := by simpa using hU
    exact ((incrementFiltration (ι := ι)).mono (Nat.le_add_left m n) _
      (T.measurableSet_time_eq m)).inter ((measurable_shift_at n m) hU')
  have hsub : A m n ⊆ {ω | ((T.andThen U).time ω : WithTop ℕ) = (n + m : ℕ)} := by
    intro ω hω
    obtain ⟨hm, _, hn⟩ := hω
    change T.time ω = m at hm
    change U.time (Bernoulli.shift^[m] ω) = n at hn
    have hs : T.suffix ω = Bernoulli.shift^[m] ω := by simp only [suffix, hm]
    change ((T.time ω + U.time (T.suffix ω) : ℕ) : WithTop ℕ) = (n + m : ℕ)
    rw [hm, hs, hn, Nat.add_comm]
  have hi : A m n ∩ {ω | ((T.andThen U).time ω : WithTop ℕ) = (n + m : ℕ)} = A m n :=
    Set.inter_eq_left.mpr hsub
  have h := ((T.andThen U).adapted.measurableSet_inter_eq_iff (A m n) (n + m)).2
    (show MeasurableSet[incrementFiltration (ι := ι) (n + m)]
      (A m n ∩ {ω | ((T.andThen U).time ω : WithTop ℕ) = (n + m : ℕ)}) from
        hi.symm ▸ hA)
  exact hi ▸ h

variable [Fintype ι] [MeasurableSingletonClass ι]

theorem measurable_sequentialWords (T U : BoundedStoppingRule ι) :
    Measurable[(T.andThen U).adapted.measurableSpace]
      (fun ω ↦ (T.stoppedWord ω, U.stoppedWord (T.suffix ω))) :=
  (T.measurable_at_andThen_left U T.stoppedWord T.measurable_stoppedWord).prodMk
    (T.measurable_at_andThen_right U U.stoppedWord U.measurable_stoppedWord)

end ExactOverlaps.StoppedConcatenation.BoundedStoppingRule
