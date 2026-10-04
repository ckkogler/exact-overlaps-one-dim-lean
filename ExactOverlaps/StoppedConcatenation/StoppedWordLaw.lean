/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.StoppedObservables
public import ExactOverlaps.StoppedConcatenation.WordPrefix
public import ExactOverlaps.StoppedConcatenation.BernoulliWordLaw
public import ExactOverlaps.StoppedConcatenation.FiniteWordSpace
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! The actual finitely supported law of an arbitrary bounded stopped word. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ExactOverlaps.StoppedConcatenation.BoundedStoppingRule

open SelfSimilar

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

noncomputable def stoppedWordProbability (T : BoundedStoppingRule ι) (p : PMF ι) :
    ProbabilityMeasure (Σ n : ℕ, Word ι n) :=
  ⟨(Bernoulli.sequenceLaw p.toMeasure).map T.stoppedWord,
    (Measure.isProbabilityMeasure_map_iff
      (T.measurable_stoppedWord.mono T.adapted.measurableSpace_le le_rfl).aemeasurable).2
      inferInstance⟩

noncomputable def stoppedWordLaw (T : BoundedStoppingRule ι) (p : PMF ι) :
    PMF (Σ n : ℕ, Word ι n) :=
  (T.stoppedWordProbability p).toMeasure.toPMF

theorem stoppedWordLaw_toMeasure (T : BoundedStoppingRule ι) (p : PMF ι) :
    (T.stoppedWordLaw p).toMeasure = (Bernoulli.sequenceLaw p.toMeasure).map T.stoppedWord := by
  unfold stoppedWordLaw
  rw [Measure.toPMF_toMeasure]
  rfl

theorem stoppedWordLaw_apply (T : BoundedStoppingRule ι) (p : PMF ι)
    (z : Σ n : ℕ, Word ι n) :
    T.stoppedWordLaw p z = Bernoulli.sequenceLaw p.toMeasure {ω | T.stoppedWord ω = z} := by
  rw [stoppedWordLaw, Measure.toPMF_apply]
  change ((Bernoulli.sequenceLaw p.toMeasure).map T.stoppedWord) {z} = _
  rw [Measure.map_apply (T.measurable_stoppedWord.mono T.adapted.measurableSpace_le le_rfl)
    (measurableSet_singleton z)]
  rfl

omit [Fintype ι] [MeasurableSingletonClass ι] in
theorem stoppedWord_eq_iff (T : BoundedStoppingRule ι) (ω : ℕ → ι)
    (n : ℕ) (w : Word ι n) :
    T.stoppedWord ω = ⟨n, w⟩ ↔ T.time ω = n ∧ Word.read n ω = w := by
  constructor
  · intro h
    have ht : T.time ω = n := congrArg Sigma.fst h
    refine ⟨ht, ?_⟩
    cases ht
    simpa only [stoppedWord, Sigma.mk.inj_iff, heq_eq_eq, true_and] using h
  · rintro ⟨ht, hw⟩
    cases ht
    exact congrArg (Sigma.mk (T.time ω)) hw

def Admissible (T : BoundedStoppingRule ι) (n : ℕ) (w : Word ι n) : Prop :=
  ∃ ω : ℕ → ι, T.time ω = n ∧ Word.read n ω = w

omit [Fintype ι] [MeasurableSingletonClass ι] in
theorem time_eq_of_admissible (T : BoundedStoppingRule ι) (n : ℕ) (w : Word ι n)
    (hw : T.Admissible n w) (ω : ℕ → ι) (hread : Word.read n ω = w) : T.time ω = n := by
  obtain ⟨ω₀, ht₀, hr₀⟩ := hw
  have hp := Word.prefix_eq_of_read_eq n (hr₀.trans hread.symm)
  have ht := T.time_eq_of_prefix_eq (ω := ω₀) (ω' := ω)
    (fun k hk ↦ hp k (by simpa only [ht₀] using hk))
  exact ht.trans ht₀

theorem stoppedWordLaw_apply_admissible (T : BoundedStoppingRule ι) (S : System ι)
    (n : ℕ) (w : Word ι n) (hw : T.Admissible n w) :
    T.stoppedWordLaw S.alphabetLaw ⟨n, w⟩ = S.wordLaw n w := by
  rw [T.stoppedWordLaw_apply]
  have he : {ω | T.stoppedWord ω = ⟨n, w⟩} = Word.read n ⁻¹' {w} := by
    ext ω
    rw [Set.mem_ofPred_eq, T.stoppedWord_eq_iff]
    change (T.time ω = n ∧ Word.read n ω = w) ↔ Word.read n ω = w
    exact ⟨And.right, fun h ↦ ⟨T.time_eq_of_admissible n w hw ω h, h⟩⟩
  rw [he, ← Measure.map_apply (Word.measurable_read n) (measurableSet_singleton w),
    S.bernoulli_read_map, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton w)]

theorem stoppedWordLaw_apply_of_not_admissible (T : BoundedStoppingRule ι) (p : PMF ι)
    (n : ℕ) (w : Word ι n) (hw : ¬T.Admissible n w) :
    T.stoppedWordLaw p ⟨n, w⟩ = 0 := by
  rw [T.stoppedWordLaw_apply]
  have he : {ω | T.stoppedWord ω = ⟨n, w⟩} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ω hω
    exact hw ⟨ω, (T.stoppedWord_eq_iff ω n w).1 hω⟩
  rw [he, measure_empty]

theorem stoppedWordLaw_support_finite (T : BoundedStoppingRule ι) (p : PMF ι) :
    (T.stoppedWordLaw p).support.Finite := by
  let f : (Σ n : Fin (T.horizon + 1), Word ι n) → Σ n : ℕ, Word ι n :=
    fun z ↦ ⟨z.1, z.2⟩
  apply (Set.finite_range f).subset
  intro z hz
  have hb : z.1 ≤ T.horizon := by
    by_contra hnot
    have he : {ω | T.stoppedWord ω = z} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      have ht : T.time ω = z.1 := congrArg Sigma.fst hω
      exact hnot (ht ▸ T.bounded ω)
    have hzero : T.stoppedWordLaw p z = 0 := by rw [T.stoppedWordLaw_apply, he, measure_empty]
    exact (show T.stoppedWordLaw p z ≠ 0 from hz) hzero
  exact ⟨⟨⟨z.1, Nat.lt_succ_of_le hb⟩, z.2⟩, rfl⟩

end ExactOverlaps.StoppedConcatenation.BoundedStoppingRule
