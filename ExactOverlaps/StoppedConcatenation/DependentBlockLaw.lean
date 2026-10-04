/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.StrongMarkovLaws
public import ExactOverlaps.Entropy.JointMixture
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-! The law of a fresh block selected using actual stopped information is the genuine PMF kernel mixture. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ExactOverlaps.StoppedConcatenation.BoundedStoppingRule

variable {ι α β : Type*} [MeasurableSpace ι] [MeasurableSpace α] [MeasurableSpace β]
  [Countable α] [MeasurableSingletonClass α]

theorem dependent_observable_map (T : BoundedStoppingRule ι)
    (p : Measure ι) [IsProbabilityMeasure p]
    (F : (ℕ → ι) → α) (hF : Measurable[T.adapted.measurableSpace] F)
    (G : α → (ℕ → ι) → β) (hG : ∀ a, Measurable (G a))
    (q : PMF α) (hq : (Bernoulli.sequenceLaw p).map F = q.toMeasure)
    (k : α → PMF β) (hk : ∀ a, (Bernoulli.sequenceLaw p).map (G a) = (k a).toMeasure) :
    (Bernoulli.sequenceLaw p).map (fun ω ↦ (F ω, G (F ω) (T.suffix ω))) =
      (Entropy.jointMixture q k).toMeasure := by
  have hFm : Measurable F := hF.mono T.adapted.measurableSpace_le le_rfl
  have hm : Measurable (fun z : α × (ℕ → ι) ↦ (z.1, G z.1 z.2)) :=
    measurable_from_prod_countable_right (fun a ↦ measurable_const.prodMk (hG a))
  have he : (fun ω ↦ (F ω, G (F ω) (T.suffix ω))) =
      (fun z : α × (ℕ → ι) ↦ (z.1, G z.1 z.2)) ∘ (fun ω ↦ (F ω, T.suffix ω)) := rfl
  rw [he, ← Measure.map_map hm (hFm.prodMk T.measurable_suffix),
    T.observable_suffix_map p F hF, hq]
  apply Measure.ext
  intro E hE
  rw [Measure.map_apply hm hE, Measure.prod_apply (hE.preimage hm), lintegral_countable',
    Entropy.jointMixture, PMF.toMeasure_bind_apply _ _ _ hE]
  apply tsum_congr
  intro a
  rw [PMF.toMeasure_apply_singleton q a (measurableSet_singleton a),
    PMF.toMeasure_map_apply _ _ _ measurable_prodMk_left hE]
  have hg : MeasurableSet ((Prod.mk a) ⁻¹' E) := hE.preimage measurable_prodMk_left
  rw [← hk a, Measure.map_apply (hG a) hg]
  exact mul_comm _ _

end ExactOverlaps.StoppedConcatenation.BoundedStoppingRule
