/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.StrongMarkovLaws
public import ExactOverlaps.StoppedConcatenation.WordMeasurability

/-! Adapted observations at the actual stopping time are measurable in its stopped sigma-algebra. -/

@[expose] public section

open MeasureTheory

namespace ExactOverlaps.StoppedConcatenation.BoundedStoppingRule

variable {ι β : Type*} [MeasurableSpace ι] [MeasurableSpace β]

theorem measurable_stopped_observable (T : BoundedStoppingRule ι)
    (F : ℕ → (ℕ → ι) → β)
    (hF : ∀ n, Measurable[incrementFiltration (ι := ι) n] (F n)) :
    Measurable[T.adapted.measurableSpace] (fun ω ↦ F (T.time ω) ω) := by
  intro E hE
  have he : (fun ω ↦ F (T.time ω) ω) ⁻¹' E =
      ⋃ n : ℕ, (F n ⁻¹' E) ∩ {ω | T.time ω = n} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨T.time ω, h, rfl⟩
    · rintro ⟨n, hn, hT⟩
      simpa only [hT] using hn
  rw [he]
  apply MeasurableSet.iUnion
  intro n
  have hm := (hF n hE).inter (T.adapted.measurableSet_eq n)
  have h := (T.adapted.measurableSet_inter_eq_iff (F n ⁻¹' E) n).2 hm
  simpa using h

variable [Fintype ι] [MeasurableSingletonClass ι]

/-- The complete observed finite word, including its length. -/
def stoppedWord (T : BoundedStoppingRule ι) (ω : ℕ → ι) : Σ n : ℕ, SelfSimilar.Word ι n :=
  ⟨T.time ω, SelfSimilar.Word.read (T.time ω) ω⟩

theorem measurable_stoppedWord (T : BoundedStoppingRule ι) :
    Measurable[T.adapted.measurableSpace] T.stoppedWord := by
  apply T.measurable_stopped_observable
    (fun n ω ↦ (⟨n, SelfSimilar.Word.read n ω⟩ : Σ n : ℕ, SelfSimilar.Word ι n))
  intro n
  exact (measurable_of_finite (Sigma.mk n)).comp (SelfSimilar.Word.measurable_read_at n)

theorem stoppedWord_suffix_map (T : BoundedStoppingRule ι)
    (p : Measure ι) [IsProbabilityMeasure p] :
    (Bernoulli.sequenceLaw p).map (fun ω ↦ (T.stoppedWord ω, T.suffix ω)) =
      ((Bernoulli.sequenceLaw p).map T.stoppedWord).prod (Bernoulli.sequenceLaw p) :=
  T.observable_suffix_map p T.stoppedWord T.measurable_stoppedWord

end ExactOverlaps.StoppedConcatenation.BoundedStoppingRule
