/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.StrongMarkovLaws
public import ExactOverlaps.StoppedConcatenation.StoppedWordLaw

/-! Almost-sure properties of a selected fresh suffix follow from its genuine stopped product law. -/

@[expose] public section

open MeasureTheory

namespace ExactOverlaps.StoppedConcatenation.BoundedStoppingRule

variable {ι α : Type*} [MeasurableSpace ι] [MeasurableSpace α]
  [Countable α] [MeasurableSingletonClass α]

theorem dependent_suffix_ae (T : BoundedStoppingRule ι) (p : PMF ι)
    (F : (ℕ → ι) → α) (hF : Measurable[T.adapted.measurableSpace] F)
    (q : PMF α) (hq : (Bernoulli.sequenceLaw p.toMeasure).map F = q.toMeasure)
    (P : α → (ℕ → ι) → Prop) (hP : ∀ a, MeasurableSet {ω | P a ω})
    (h : ∀ a ∈ q.support, ∀ᵐ ω ∂Bernoulli.sequenceLaw p.toMeasure, P a ω) :
    ∀ᵐ ω ∂Bernoulli.sequenceLaw p.toMeasure, P (F ω) (T.suffix ω) := by
  have hset : MeasurableSet {z : α × (ℕ → ι) | P z.1 z.2} := by
    have he : {z : α × (ℕ → ι) | P z.1 z.2} = ⋃ a : α, {a} ×ˢ {ω | P a ω} := by
      ext z
      simp
    rw [he]
    exact MeasurableSet.iUnion (fun a ↦ (measurableSet_singleton a).prod (hP a))
  have ha : ∀ᵐ a ∂q.toMeasure, a ∈ q.support := by
    change q.support ∈ ae q.toMeasure
    rw [mem_ae_iff_prob_eq_one q.support_countable.measurableSet,
      PMF.toMeasure_apply_eq_one_iff _ q.support_countable.measurableSet]
  have hp : ∀ᵐ z ∂q.toMeasure.prod (Bernoulli.sequenceLaw p.toMeasure), P z.1 z.2 :=
    (Measure.ae_prod_iff_ae_ae hset).mpr (ha.mono (fun a ha ↦ h a ha))
  have hlaw := T.observable_suffix_map p.toMeasure F hF
  rw [hq] at hlaw
  rw [← hlaw] at hp
  have hFm : Measurable F := hF.mono T.adapted.measurableSpace_le le_rfl
  exact (ae_map_iff (hFm.prodMk T.measurable_suffix).aemeasurable hset).mp hp

end ExactOverlaps.StoppedConcatenation.BoundedStoppingRule
