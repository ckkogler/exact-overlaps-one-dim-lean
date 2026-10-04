/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.WordScalars

/-! Positive-mass stopped-word bounds imply bounds for the genuine Bernoulli process. -/

@[expose] public section

noncomputable section
open MeasureTheory

namespace ExactOverlaps.SelfSimilar.System

open StoppedConcatenation

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem stoppedWord_ae_of_support (S : System ι) (T : BoundedStoppingRule ι)
    (P : (Σ n : ℕ, Word ι n) → Prop)
    (hP : ∀ z ∈ (T.stoppedWordLaw S.alphabetLaw).support, P z) :
    ∀ᵐ ω ∂Bernoulli.sequenceLaw S.alphabetLaw.toMeasure, P (T.stoppedWord ω) := by
  have hset : MeasurableSet {z | P z} := (Set.to_countable _).measurableSet
  have h : ∀ᵐ z ∂(T.stoppedWordLaw S.alphabetLaw).toMeasure, P z := by
    change {z | P z} ∈ ae (T.stoppedWordLaw S.alphabetLaw).toMeasure
    rw [mem_ae_iff_prob_eq_one hset]
    exact (PMF.toMeasure_apply_eq_one_iff _ hset).mpr hP
  rw [T.stoppedWordLaw_toMeasure] at h
  exact (ae_map_iff
    (T.measurable_stoppedWord.mono T.adapted.measurableSpace_le le_rfl).aemeasurable hset).mp h

theorem relative_scale_ae_of_support (S : System ι) (T : BoundedStoppingRule ι)
    (r ε : ℝ)
    (h : ∀ z ∈ (T.stoppedWordLaw S.alphabetLaw).support,
      r < ε * |S.totalWordRatio z|) :
    ∀ᵐ ω ∂Bernoulli.sequenceLaw S.alphabetLaw.toMeasure,
      r < ε * |S.prefixRatio (T.time ω) ω| := by
  have hh := S.stoppedWord_ae_of_support T (fun z ↦ r < ε * |S.totalWordRatio z|) h
  simpa only [totalWordRatio, BoundedStoppingRule.stoppedWord, S.wordRatio_read] using hh

end ExactOverlaps.SelfSimilar.System
