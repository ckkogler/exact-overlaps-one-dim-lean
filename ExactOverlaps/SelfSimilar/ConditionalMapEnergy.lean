module

public import ExactOverlaps.SelfSimilar.ConditionalFunctionalTower
public import ExactOverlaps.SelfSimilar.FiniteLawMixtureBounds
public import ExactOverlaps.SelfSimilar.RatioConditioning

/-! Actual mean variance energy of a statistic after a finite observation. -/

@[expose] public section

open scoped ENNReal BigOperators

namespace ExactOverlaps.SelfSimilar

open Entropy EntropyEnergyGap VarianceEnergy FiniteProbability

noncomputable def meanConditionalMapEnergy {α β : Type*}
    (p : PMF α) (hp : p.support.Finite) (f : α → β) (B : α → ℝ) (r : ℝ) : ℝ :=
  meanFiberFunctional p hp f (fun q _ ↦ (energyBelow (q.map B).toMeasure r).toReal)

theorem meanConditionalMapEnergy_le {α β : Type*}
    (p : PMF α) (hp : p.support.Finite) (f : α → β) (B : α → ℝ) (r : ℝ) :
    meanConditionalMapEnergy p hp f B r ≤ (energyBelow (p.map B).toMeasure r).toReal := by
  rw [meanConditionalMapEnergy, meanFiberFunctional_eq_sum]
  exact average_mapped_conditional_energyBelow_le p hp f B r

theorem meanConditionalMapEnergy_refinement_le {α β γ : Type*}
    (p : PMF α) (hp : p.support.Finite) (f : α → β) (k : β → γ) (B : α → ℝ) (r : ℝ) :
    meanConditionalMapEnergy p hp f B r ≤
      meanConditionalMapEnergy p hp (fun a ↦ k (f a)) B r := by
  exact meanFiberFunctional_refinement_le p hp f k
    (fun q _ ↦ (energyBelow (q.map B).toMeasure r).toReal)
    (fun q hq ↦ meanConditionalMapEnergy_le q hq f B r)

theorem meanConditionalMapEnergy_congr_fibers {α β γ : Type*}
    (p : PMF α) (hp : p.support.Finite) (f : α → β) (g : α → γ) (B : α → ℝ) (r : ℝ)
    (hfg : ∀ a b, f a = f b ↔ g a = g b) :
    meanConditionalMapEnergy p hp f B r = meanConditionalMapEnergy p hp g B r :=
  meanFiberFunctional_congr_fibers p hp f g
    (fun q _ ↦ (energyBelow (q.map B).toMeasure r).toReal) hfg

namespace System

variable {ι : Type*} [Fintype ι]

/-- Mean energy of the actual random word translation conditional on its signed ratio. -/
noncomputable def meanRatioTranslationEnergy (S : System ι) (n : ℕ) (r : ℝ) : ℝ :=
  meanConditionalMapEnergy (S.wordLaw n) (Set.toFinite _) (S.wordRatio n) (S.wordTranslation n) r

theorem meanRatioTranslationEnergy_eq_sum (S : System ι) (n : ℕ) (r : ℝ) :
    S.meanRatioTranslationEnergy n r =
      (letI : Fintype (S.wordRatioLaw n).support := (S.wordRatioLaw_support_finite n).fintype
      ∑ t : (S.wordRatioLaw n).support, (S.wordRatioLaw n t).toReal *
        (energyBelow (S.ratioTranslationLaw n t).toMeasure r).toReal) := by
  rw [meanRatioTranslationEnergy, meanConditionalMapEnergy, meanFiberFunctional_eq_sum]
  rfl

theorem meanRatioTranslationEnergy_nonneg (S : System ι) (n : ℕ) (r : ℝ) :
    0 ≤ S.meanRatioTranslationEnergy n r := by
  rw [S.meanRatioTranslationEnergy_eq_sum]
  exact Finset.sum_nonneg (fun _ _ ↦ mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)

end System
end ExactOverlaps.SelfSimilar
