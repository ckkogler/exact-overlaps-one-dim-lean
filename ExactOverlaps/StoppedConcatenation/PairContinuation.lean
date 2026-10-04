/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.SequentialObservations
public import ExactOverlaps.StoppedConcatenation.DependentWordLaw

/-! Actual continuation after two observed stopped blocks, retaining both observations. -/

@[expose] public section

open MeasureTheory

namespace ExactOverlaps.StoppedConcatenation.BoundedStoppingRule

open SelfSimilar

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

def afterPair (T U : BoundedStoppingRule ι)
    (V : (Σ n : ℕ, Word ι n) × (Σ n : ℕ, Word ι n) → BoundedStoppingRule ι)
    (N : ℕ) (hN : ∀ z, (V z).horizon ≤ N) : BoundedStoppingRule ι :=
  (T.andThen U).andThenChoice
    (fun ω ↦ (T.stoppedWord ω, U.stoppedWord (T.suffix ω)))
    (T.measurable_sequentialWords U) V N hN

theorem stoppedWord_afterPair (T U : BoundedStoppingRule ι)
    (V : (Σ n : ℕ, Word ι n) × (Σ n : ℕ, Word ι n) → BoundedStoppingRule ι)
    (N : ℕ) (hN : ∀ z, (V z).horizon ≤ N) (ω : ℕ → ι) :
    (T.afterPair U V N hN).stoppedWord ω =
      Word.concatenate (Word.concatenate (T.stoppedWord ω) (U.stoppedWord (T.suffix ω)))
        ((V (T.stoppedWord ω, U.stoppedWord (T.suffix ω))).stoppedWord ((T.andThen U).suffix ω)) := by
  have hh := Word.read_append ((T.andThen U).time ω)
    ((V (T.stoppedWord ω, U.stoppedWord (T.suffix ω))).time ((T.andThen U).suffix ω)) ω
  have hw : (T.afterPair U V N hN).stoppedWord ω =
      Word.concatenate ((T.andThen U).stoppedWord ω)
        ((V (T.stoppedWord ω, U.stoppedWord (T.suffix ω))).stoppedWord ((T.andThen U).suffix ω)) := by
    change (⟨(T.andThen U).time ω +
        (V (T.stoppedWord ω, U.stoppedWord (T.suffix ω))).time ((T.andThen U).suffix ω),
        Word.read ((T.andThen U).time ω +
          (V (T.stoppedWord ω, U.stoppedWord (T.suffix ω))).time ((T.andThen U).suffix ω)) ω⟩ :
      Σ n, Word ι n) = _
    rw [Nat.add_comm ((T.andThen U).time ω)]
    exact congrArg (Sigma.mk _) hh
  rwa [T.stoppedWord_andThen U ω] at hw

theorem afterPair_stoppedWordLaw (T U : BoundedStoppingRule ι)
    (V : (Σ n : ℕ, Word ι n) × (Σ n : ℕ, Word ι n) → BoundedStoppingRule ι)
    (N : ℕ) (hN : ∀ z, (V z).horizon ≤ N) (p : PMF ι) :
    (T.afterPair U V N hN).stoppedWordLaw p =
      (Entropy.jointMixture (Entropy.independentPair (T.stoppedWordLaw p) (U.stoppedWordLaw p))
        (fun z ↦ (V z).stoppedWordLaw p)).map
          (fun z ↦ Word.concatenate (Word.concatenate z.1.1 z.1.2) z.2) := by
  let F := fun ω ↦ (T.stoppedWord ω, U.stoppedWord (T.suffix ω))
  have hFm : Measurable F := (T.measurable_sequentialWords U).mono
    (T.andThen U).adapted.measurableSpace_le le_rfl
  have hV (z) : Measurable (V z).stoppedWord :=
    (V z).measurable_stoppedWord.mono (V z).adapted.measurableSpace_le le_rfl
  have hlaw := (T.andThen U).dependent_observable_map p.toMeasure F
    (T.measurable_sequentialWords U) (fun z ↦ (V z).stoppedWord) hV
    (Entropy.independentPair (T.stoppedWordLaw p) (U.stoppedWordLaw p))
    (T.sequential_stoppedWord_map U p) (fun z ↦ (V z).stoppedWordLaw p)
    (fun z ↦ ((V z).stoppedWordLaw_toMeasure p).symm)
  apply PMF.toMeasure_injective
  rw [(T.afterPair U V N hN).stoppedWordLaw_toMeasure,
    ← PMF.toMeasure_map _ _ (measurable_of_countable _), ← hlaw]
  have hG : Measurable (fun z : ((Σ n : ℕ, Word ι n) × (Σ n : ℕ, Word ι n)) ×
      (ℕ → ι) ↦ (V z.1).stoppedWord z.2) :=
    measurable_from_prod_countable_right hV
  have hp : Measurable (fun ω ↦ (F ω, (V (F ω)).stoppedWord ((T.andThen U).suffix ω))) :=
    hFm.prodMk (hG.comp (hFm.prodMk (T.andThen U).measurable_suffix))
  rw [Measure.map_map (measurable_of_countable _) hp]
  congr 1
  funext ω
  exact T.stoppedWord_afterPair U V N hN ω

end ExactOverlaps.StoppedConcatenation.BoundedStoppingRule
