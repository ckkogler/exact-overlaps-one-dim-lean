/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.HeadEmbedding

/-! Explicit bounded start rules for every prescribed block, with genuine ordered nonoverlap. -/

@[expose] public section

open MeasureTheory
open scoped Classical

namespace ExactOverlaps.StoppedConcatenation

open SelfSimilar

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

def HasBlockStarts (S : System ι) (m : ℕ) (τ : Fin (m + 1) → BoundedStoppingRule ι)
    (A : BoundedStoppingRule ι) : Prop :=
  ∃ starts : Fin (m + 1) → BoundedStoppingRule ι,
    (∀ ω, (starts (Fin.last m)).time ω = A.time ω) ∧
    ∀ i : Fin m, ∀ᵐ ω ∂Bernoulli.sequenceLaw S.alphabetLaw.toMeasure,
      ((starts i.castSucc).andThen (τ i.castSucc)).time ω ≤ (starts i.succ).time ω

omit [MeasurableSingletonClass ι] in
theorem hasBlockStarts_single (S : System ι) (τ : Fin 1 → BoundedStoppingRule ι)
    (A : BoundedStoppingRule ι) : HasBlockStarts S 0 τ A := by
  refine ⟨fun _ ↦ A, fun _ ↦ rfl, ?_⟩
  intro i
  exact Fin.elim0 i

theorem hasBlockStarts_head (S : System ι) (m : ℕ)
    (τ : Fin (m + 2) → BoundedStoppingRule ι) (G : BoundedStoppingRule ι)
    (A : (headLabelLaw S G (τ 0)).support → BoundedStoppingRule ι)
    (hA : ∀ b, HasBlockStarts S m (fun j ↦ τ j.succ) (A b)) :
    HasBlockStarts S (m + 1) τ (headContinuation S G (τ 0) A) := by
  choose starts hlast horder using hA
  let globalStarts : Fin (m + 2) → BoundedStoppingRule ι :=
    Fin.cases G (fun j ↦ headContinuation S G (τ 0) (fun b ↦ starts b j))
  refine ⟨globalStarts, ?_, ?_⟩
  · intro ω
    change (headContinuation S G (τ 0) (fun b ↦ starts b (Fin.last m))).time ω = _
    exact headContinuation_time_congr S G (τ 0) _ A hlast ω
  · intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact Filter.Eventually.of_forall (fun ω ↦ headContinuation_after_head S G (τ 0)
        (fun b ↦ starts b 0) ω)
    · exact headContinuation_ordered_ae S G (τ 0) (τ j.succ.castSucc)
        (fun b ↦ starts b j.castSucc) (fun b ↦ starts b j.succ) (fun b ↦ horder b j)

end ExactOverlaps.StoppedConcatenation
