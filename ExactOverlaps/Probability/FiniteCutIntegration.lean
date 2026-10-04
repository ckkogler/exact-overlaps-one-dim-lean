module

public import ExactOverlaps.Probability.NonnegativeExpectations
public import ExactOverlaps.Probability.HalfLineIntegration

/-!
# Integrating cuts relative to each finite sample

Finite averaging commutes with nonnegative integration. Each sample may use
its own splitting point, after which both halves use the same positive
displacement variable. No integrability premise is required.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ExactOverlaps.FiniteProbability

lemma lintegral_expectation_translated_halflines {α : Type*} (p : PMF α)
    (hp : p.support.Finite) (c : α → ℝ) (F : ℝ → α → ℝ)
    (hm : ∀ a ∈ p.support, Measurable (fun t ↦ F t a))
    (hn : ∀ a ∈ p.support, ∀ t, 0 ≤ F t a) :
    (∫⁻ t, ENNReal.ofReal (expectation p hp (F t))) =
      (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (expectation p hp (fun a ↦ F (c a - u) a))) +
      ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (expectation p hp (fun a ↦ F (c a + u) a)) := by
  rw [lintegral_ofReal_expectation volume p hp F hm hn,
    lintegral_ofReal_expectation (volume.restrict (Ioi 0)) p hp
      (fun u a ↦ F (c a - u) a)
      (fun a ha ↦ (hm a ha).comp (measurable_const.sub measurable_id))
      (fun a ha u ↦ hn a ha _),
    lintegral_ofReal_expectation (volume.restrict (Ioi 0)) p hp
      (fun u a ↦ F (c a + u) a)
      (fun a ha ↦ (hm a ha).comp (measurable_const.add measurable_id))
      (fun a ha u ↦ hn a ha _), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [lintegral_eq_translated_halflines (fun t ↦ ENNReal.ofReal (F t a))
    ((hm a (by simpa using ha)).ennreal_ofReal) (c a), mul_add]

end ExactOverlaps.FiniteProbability
