/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.SequentialRules

/-! Almost-sure ordering can be repaired by genuine bounded stopping-time maxima. -/

@[expose] public section

open MeasureTheory

namespace ExactOverlaps.StoppedConcatenation.BoundedStoppingRule

variable {ι : Type*} [MeasurableSpace ι]

def maxRule (T U : BoundedStoppingRule ι) : BoundedStoppingRule ι where
  time := fun ω ↦ max (T.time ω) (U.time ω)
  horizon := max T.horizon U.horizon
  bounded := fun ω ↦ max_le_max (T.bounded ω) (U.bounded ω)
  adapted := by
    intro n
    have h := (T.measurableSet_time_le n).inter (U.measurableSet_time_le n)
    convert h using 1
    ext ω
    change ((max (T.time ω) (U.time ω) : ℕ) : WithTop ℕ) ≤ (n : WithTop ℕ) ↔
      T.time ω ≤ n ∧ U.time ω ≤ n
    exact_mod_cast (max_le_iff : max (T.time ω) (U.time ω) ≤ n ↔
      T.time ω ≤ n ∧ U.time ω ≤ n)

def orderedRepair (τ S : ℕ → BoundedStoppingRule ι) : ℕ → BoundedStoppingRule ι
  | 0 => S 0
  | n + 1 => maxRule (S (n + 1)) ((orderedRepair τ S n).andThen (τ n))

theorem orderedRepair_end_le_succ (τ S : ℕ → BoundedStoppingRule ι)
    (n : ℕ) (ω : ℕ → ι) :
    ((orderedRepair τ S n).andThen (τ n)).time ω ≤ (orderedRepair τ S (n + 1)).time ω :=
  le_max_right _ _

theorem orderedRepair_monotone (τ S : ℕ → BoundedStoppingRule ι) (ω : ℕ → ι) :
    Monotone (fun n ↦ (orderedRepair τ S n).time ω) := by
  apply monotone_nat_of_le_succ
  intro n
  exact (Nat.le_add_right _ _).trans (orderedRepair_end_le_succ τ S n ω)

theorem orderedRepair_end_le (τ S : ℕ → BoundedStoppingRule ι)
    {i j : ℕ} (hij : i < j) (ω : ℕ → ι) :
    ((orderedRepair τ S i).andThen (τ i)).time ω ≤ (orderedRepair τ S j).time ω :=
  (orderedRepair_end_le_succ τ S i ω).trans
    (orderedRepair_monotone τ S ω (Nat.succ_le_iff.mpr hij))

theorem orderedRepair_time_ae (τ S : ℕ → BoundedStoppingRule ι)
    (μ : Measure (ℕ → ι)) (n : ℕ)
    (horder : ∀ k < n, ∀ᵐ ω ∂μ, ((S k).andThen (τ k)).time ω ≤ (S (k + 1)).time ω) :
    (orderedRepair τ S n).time =ᵐ[μ] (S n).time := by
  induction n with
  | zero => exact Filter.Eventually.of_forall (fun _ ↦ rfl)
  | succ n ih =>
    have hn := ih (fun k hk ↦ horder k (Nat.lt_succ_of_lt hk))
    filter_upwards [hn, horder n (Nat.lt_succ_self n)] with ω he hle
    have hs : (orderedRepair τ S n).suffix ω = (S n).suffix ω := by
      simp only [suffix, he]
    change max ((S (n + 1)).time ω)
      ((orderedRepair τ S n).time ω + (τ n).time ((orderedRepair τ S n).suffix ω)) = _
    rw [he, hs]
    exact max_eq_left hle

end ExactOverlaps.StoppedConcatenation.BoundedStoppingRule
