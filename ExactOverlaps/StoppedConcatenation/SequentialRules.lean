/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.BoundedStrongMarkov

/-! Sequential use of two bounded rules is again a genuine bounded stopping time. -/

@[expose] public section

open MeasureTheory

namespace ExactOverlaps.StoppedConcatenation

variable {ι : Type*} [MeasurableSpace ι]

theorem measurable_shift_at (n k : ℕ) :
    @Measurable (ℕ → ι) (ℕ → ι) (incrementFiltration (n + k))
      (incrementFiltration n) (Bernoulli.shift^[k]) := by
  apply Measurable.of_comap_le
  change (⨆ j : Fin n,
    MeasurableSpace.comap (fun ω : ℕ → ι ↦ ω j) inferInstance).comap
      (Bernoulli.shift^[k]) ≤
        ⨆ j : Fin (n + k), MeasurableSpace.comap (fun ω : ℕ → ι ↦ ω j) inferInstance
  rw [MeasurableSpace.comap_iSup]
  apply iSup_le
  intro j
  rw [MeasurableSpace.comap_comp]
  have he : (fun ω : ℕ → ι ↦ ω j) ∘ Bernoulli.shift^[k] =
      fun ω : ℕ → ι ↦ ω (j + k) := by
    funext ω
    exact Bernoulli.shift_iterate k ω j
  rw [he]
  exact le_iSup_of_le (⟨j + k, by omega⟩ : Fin (n + k)) le_rfl

namespace BoundedStoppingRule

variable (T U : BoundedStoppingRule ι)

theorem adapted_sequential : IsStoppingTime incrementFiltration
    (fun ω ↦ ((T.time ω + U.time (T.suffix ω) : ℕ) : WithTop ℕ)) := by
  intro n
  suffices hm : MeasurableSet[incrementFiltration (ι := ι) n]
      {ω | T.time ω + U.time (T.suffix ω) ≤ n} by
    convert hm using 1
    ext ω
    change (((T.time ω + U.time (T.suffix ω) : ℕ) : WithTop ℕ) ≤ (n : WithTop ℕ)) ↔ _
    exact_mod_cast (Iff.rfl : T.time ω + U.time (T.suffix ω) ≤ n ↔
      T.time ω + U.time (T.suffix ω) ≤ n)
  have he : {ω | T.time ω + U.time (T.suffix ω) ≤ n} =
      ⋃ k : Fin (n + 1), {ω | T.time ω = k} ∩
        (Bernoulli.shift^[(k : ℕ)]) ⁻¹' {ω | U.time ω ≤ n - k} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · intro h
      refine ⟨⟨T.time ω, by omega⟩, rfl, ?_⟩
      change U.time (T.suffix ω) ≤ n - T.time ω
      omega
    · rintro ⟨k, hk, hU⟩
      have hs : T.suffix ω = Bernoulli.shift^[(k : ℕ)] ω := by simp only [suffix, hk]
      rw [hs, hk]
      omega
  rw [he]
  apply MeasurableSet.iUnion
  intro k
  have hk : (k : ℕ) ≤ n := by omega
  have hT := (incrementFiltration (ι := ι)).mono hk _ (T.measurableSet_time_eq k)
  have hU := (measurable_shift_at (ι := ι) (n - k) k) (U.measurableSet_time_le (n - k))
  have heq : n - (k : ℕ) + k = n := Nat.sub_add_cancel hk
  rw [heq] at hU
  exact hT.inter hU

def andThen : BoundedStoppingRule ι where
  time := fun ω ↦ T.time ω + U.time (T.suffix ω)
  horizon := T.horizon + U.horizon
  bounded := fun ω ↦ Nat.add_le_add (T.bounded ω) (U.bounded (T.suffix ω))
  adapted := T.adapted_sequential U

theorem suffix_andThen (ω : ℕ → ι) :
    (T.andThen U).suffix ω = U.suffix (T.suffix ω) := by
  change Bernoulli.shift^[T.time ω + U.time (T.suffix ω)] ω =
    Bernoulli.shift^[U.time (T.suffix ω)] (Bernoulli.shift^[T.time ω] ω)
  rw [Nat.add_comm, Function.iterate_add_apply]

end BoundedStoppingRule
end ExactOverlaps.StoppedConcatenation
