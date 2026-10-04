/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.WordMeasurability

/-! The countable disjoint union of finite word spaces has measurable singletons. -/

@[expose] public section

open MeasureTheory

namespace ExactOverlaps.SelfSimilar.Word

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

instance finiteWordMeasurableSingleton : MeasurableSingletonClass (Σ n : ℕ, Word ι n) where
  measurableSet_singleton z := by
    change MeasurableSet[⨅ n : ℕ,
      (inferInstance : MeasurableSpace (Word ι n)).map (Sigma.mk n)] {z}
    rw [MeasurableSpace.measurableSet_iInf]
    intro n
    change MeasurableSet (Sigma.mk n ⁻¹' {z})
    exact (Set.toFinite (Sigma.mk n ⁻¹' {z})).measurableSet

end ExactOverlaps.SelfSimilar.Word
