/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.SelfSimilar.BernoulliBlocks
public import Mathlib.Probability.Process.Stopping

/-!
Bounded stopping times for the filtration of the first n increments.
At time zero this filtration contains no coordinate information.
-/

@[expose] public section

open MeasureTheory

namespace ExactOverlaps.StoppedConcatenation

variable {ι : Type*} [MeasurableSpace ι]

/-- Unlike the earlier approximation filtration, time n observes exactly n symbols. -/
def incrementFiltration : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → ι)) where
  seq n := ⨆ k : Fin n, MeasurableSpace.comap (fun ω : ℕ → ι ↦ ω k) inferInstance
  mono' n m hnm := by
    apply iSup_le
    intro k
    exact le_iSup_of_le (⟨k, by omega⟩ : Fin m) le_rfl
  le' n := iSup_le (fun k ↦ (measurable_pi_apply (k : ℕ)).comap_le)

theorem incrementFiltration_eq_comap_block (n : ℕ) :
    incrementFiltration (ι := ι) n =
      MeasurableSpace.comap (Bernoulli.block n 0) inferInstance := by
  have heq : Bernoulli.block (A := ι) n 0 =
      fun (ω : ℕ → ι) (k : Fin n) ↦ ω k := by
    funext ω k
    exact congrArg ω (Nat.zero_add _)
  rw [heq, MeasurableSpace.comap_process_pi]
  rfl

theorem incrementFiltration_zero : incrementFiltration (ι := ι) 0 = ⊥ := by
  change (⨆ k : Fin 0,
    MeasurableSpace.comap (fun ω : ℕ → ι ↦ ω k) inferInstance) = ⊥
  simp

/-- Actual bounded Mathlib stopping times; adaptedness is not an extra abstract oracle. -/
structure BoundedStoppingRule (ι : Type*) [MeasurableSpace ι] where
  time : (ℕ → ι) → ℕ
  horizon : ℕ
  bounded : ∀ ω, time ω ≤ horizon
  adapted : IsStoppingTime incrementFiltration (fun ω ↦ (time ω : WithTop ℕ))

namespace BoundedStoppingRule

variable (T : BoundedStoppingRule ι)

theorem measurableSet_time_le (n : ℕ) :
    MeasurableSet[incrementFiltration (ι := ι) n] {ω | T.time ω ≤ n} := by
  simpa using T.adapted n

theorem time_le_iff_of_prefix_eq (n : ℕ) {ω ω' : ℕ → ι}
    (h : ∀ k < n, ω k = ω' k) :
    T.time ω ≤ n ↔ T.time ω' ≤ n := by
  have hm := T.measurableSet_time_le n
  rw [incrementFiltration_eq_comap_block, MeasurableSpace.measurableSet_comap] at hm
  obtain ⟨s, _, hs⟩ := hm
  have hb : Bernoulli.block n 0 ω = Bernoulli.block n 0 ω' := by
    funext k
    simpa only [Bernoulli.block, Nat.zero_add] using h k k.isLt
  have he : ω ∈ Bernoulli.block n 0 ⁻¹' s ↔ ω' ∈ Bernoulli.block n 0 ⁻¹' s := by
    simp only [Set.mem_preimage, hb]
  simpa only [hs, Set.mem_ofPred_eq] using he

/-- The stopped time is completely determined by the symbols it has observed. -/
theorem time_eq_of_prefix_eq {ω ω' : ℕ → ι}
    (h : ∀ k < T.time ω, ω k = ω' k) : T.time ω' = T.time ω := by
  have hle : T.time ω' ≤ T.time ω :=
    (T.time_le_iff_of_prefix_eq (T.time ω) h).1 le_rfl
  apply le_antisymm hle
  exact (T.time_le_iff_of_prefix_eq (T.time ω')
    (fun k hk ↦ h k (lt_of_lt_of_le hk hle))).2 le_rfl

theorem time_eq_of_horizon_prefix_eq {ω ω' : ℕ → ι}
    (h : ∀ k < T.horizon, ω k = ω' k) : T.time ω' = T.time ω :=
  T.time_eq_of_prefix_eq (fun k hk ↦ h k (lt_of_lt_of_le hk (T.bounded ω)))

def constant (n : ℕ) : BoundedStoppingRule ι where
  time := fun _ ↦ n
  horizon := n
  bounded := fun _ ↦ le_rfl
  adapted := isStoppingTime_const _ n

end BoundedStoppingRule
end ExactOverlaps.StoppedConcatenation
