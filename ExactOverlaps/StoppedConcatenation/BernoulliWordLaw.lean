/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.WordMeasurability
public import ExactOverlaps.SelfSimilar.CodingLaw
public import ExactOverlaps.Entropy.DiscreteMeasureConvolution

/-! The existing product word PMF is precisely the law of the actual Bernoulli prefix. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem bernoulli_read_map (S : System ι) (n : ℕ) :
    (Bernoulli.sequenceLaw S.alphabetLaw.toMeasure).map (Word.read n) =
      (S.wordLaw n).toMeasure := by
  induction n with
  | zero =>
    change (Bernoulli.sequenceLaw S.alphabetLaw.toMeasure).map
      (fun _ ↦ PUnit.unit) = (show PMF PUnit from S.wordLaw 0).toMeasure
    have hp : (show PMF PUnit from S.wordLaw 0) = PMF.pure PUnit.unit := by
      apply PMF.ext
      intro w
      cases w
      change (1 : ℝ≥0∞) = PMF.pure PUnit.unit PUnit.unit
      simp [PMF.pure_apply]
    rw [hp, PMF.toMeasure_pure]
    change (Bernoulli.sequenceLaw S.alphabetLaw.toMeasure).map
      (fun _ ↦ PUnit.unit) = _
    simp
  | succ n ih =>
    change (Bernoulli.sequenceLaw S.alphabetLaw.toMeasure).map
      (fun ω ↦ (ω 0, Word.read n (Bernoulli.shift ω))) =
        (show PMF (ι × Word ι n) from S.wordLaw (n + 1)).toMeasure
    have hp : (show PMF (ι × Word ι n) from S.wordLaw (n + 1)) =
        Entropy.independentPair S.alphabetLaw (S.wordLaw n) := by
      apply PMF.ext
      rintro ⟨a, v⟩
      change (S.weight a : ℝ≥0∞) * S.wordWeight n v = _
      rw [Entropy.independentPair_apply]
      rfl
    rw [hp, Entropy.independentPair_toMeasure]
    have he : (fun ω : ℕ → ι ↦ (ω 0, Word.read n (Bernoulli.shift ω))) =
        (Prod.map id (Word.read n)) ∘ (fun ω ↦ (ω 0, Bernoulli.shift ω)) := rfl
    rw [he, ← Measure.map_map (measurable_id.prodMap (Word.measurable_read n))
      ((measurable_pi_apply 0).prodMk Bernoulli.measurable_shift),
      Bernoulli.head_shift_map, ← Measure.map_prod_map _ _ measurable_id (Word.measurable_read n),
      Measure.map_id, ih]

end ExactOverlaps.SelfSimilar.System
