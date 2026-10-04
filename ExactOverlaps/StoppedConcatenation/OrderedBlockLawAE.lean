/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.OrderedBlockLaw
public import ExactOverlaps.StoppedConcatenation.OrderedBlockRepair

/-! The original almost-sure ordered block family has the exact independent product law. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Classical

namespace ExactOverlaps.StoppedConcatenation.BoundedStoppingRule

open SelfSimilar

variable {ι : Type*} [MeasurableSpace ι]

def extendRules {n : ℕ} (T : Fin n → BoundedStoppingRule ι) (k : ℕ) : BoundedStoppingRule ι :=
  if hk : k < n then T ⟨k, hk⟩ else constant 0

theorem extendRules_at {n : ℕ} (T : Fin n → BoundedStoppingRule ι) (i : Fin n) :
    extendRules T i = T i := by simp only [extendRules, dite_eq_left i.isLt]

variable [Fintype ι] [MeasurableSingletonClass ι]

theorem independent_ae_ordered_blocks (m : ℕ)
    (S τ : Fin (m + 1) → BoundedStoppingRule ι) (p : PMF ι)
    (horder : ∀ i : Fin m, ∀ᵐ ω ∂Bernoulli.sequenceLaw p.toMeasure,
      ((S i.castSucc).andThen (τ i.castSucc)).time ω ≤ (S i.succ).time ω) :
    iIndepFun (fun j ω ↦ (τ j).stoppedWord ((S j).suffix ω))
      (Bernoulli.sequenceLaw p.toMeasure) := by
  let R : Fin (m + 1) → BoundedStoppingRule ι :=
    fun i ↦ orderedRepair (extendRules τ) (extendRules S) i
  have htime (i : Fin (m + 1)) : (R i).time =ᵐ[Bernoulli.sequenceLaw p.toMeasure] (S i).time := by
    have hh := orderedRepair_time_ae (extendRules τ) (extendRules S)
      (Bernoulli.sequenceLaw p.toMeasure) i.val (fun k hk ↦ ?_)
    · rw [extendRules_at] at hh
      exact hh
    · have hk' : k < m := lt_of_lt_of_le hk (Nat.le_of_lt_succ i.isLt)
      have h := horder ⟨k, hk'⟩
      simpa only [extendRules, dite_eq_left (Nat.lt_succ_of_lt hk'),
        dite_eq_left (Nat.succ_lt_succ hk'), Fin.castSucc_mk, Fin.succ_mk] using h
  have hrep : ∀ i j : Fin (m + 1), i < j → ∀ ω,
      ((R i).andThen (τ i)).time ω ≤ (R j).time ω := by
    intro i j hij ω
    have h := orderedRepair_end_le (extendRules τ) (extendRules S)
      (show i.val < j.val from hij) ω
    simpa only [extendRules_at] using h
  have heq (i : Fin (m + 1)) :
      (fun ω ↦ (τ i).stoppedWord ((R i).suffix ω)) =ᵐ[Bernoulli.sequenceLaw p.toMeasure]
        (fun ω ↦ (τ i).stoppedWord ((S i).suffix ω)) := by
    filter_upwards [htime i] with ω hω
    have hs : (R i).suffix ω = (S i).suffix ω := by simp only [suffix, hω]
    exact congrArg (τ i).stoppedWord hs
  exact (independent_ordered_blocks R τ p hrep).congr heq

theorem ae_ordered_blocks_joint_map (m : ℕ)
    (S τ : Fin (m + 1) → BoundedStoppingRule ι) (p : PMF ι)
    (horder : ∀ i : Fin m, ∀ᵐ ω ∂Bernoulli.sequenceLaw p.toMeasure,
      ((S i.castSucc).andThen (τ i.castSucc)).time ω ≤ (S i.succ).time ω) :
    (Bernoulli.sequenceLaw p.toMeasure).map (fun ω j ↦ (τ j).stoppedWord ((S j).suffix ω)) =
      Measure.pi (fun j ↦ ((τ j).stoppedWordLaw p).toMeasure) := by
  have h := (independent_ae_ordered_blocks m S τ p horder).map_fun_eq_pi_map
    (fun j ↦ (measurable_block_after_start (S j) (τ j)).aemeasurable)
  simpa only [block_after_start_map] using h

end ExactOverlaps.StoppedConcatenation.BoundedStoppingRule
