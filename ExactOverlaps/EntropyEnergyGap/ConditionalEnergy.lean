module

public import ExactOverlaps.EntropyEnergyGap.FiniteMixtures
public import ExactOverlaps.Probability.FinitePoissonReal
public import ExactOverlaps.Probability.FiberAverages

/-!
# Real conditional-energy Jensen for finite laws

Every conditional PMF has finite support, and all relevant variance
energies are proved finite before converting the mixture inequality to
ordinary real numbers.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal Classical
open ExactOverlaps.Entropy ExactOverlaps.VarianceEnergy ExactOverlaps.FiniteProbability

namespace ExactOverlaps.EntropyEnergyGap

lemma finiteLaw_energyBelow_ne_top (p : PMF ℝ) (hp : p.support.Finite) (R : ℝ) :
    energyBelow p.toMeasure R ≠ ∞ := by
  exact ne_of_lt ((energyBelow_le_energy p.toMeasure R).trans_lt
    (lt_top_iff_ne_top.mpr (ExactOverlaps.Poisson.finiteLaw_energy_ne_top p hp)))

theorem mean_conditional_energyBelow_le {β : Type*} (p : PMF ℝ) (hp : p.support.Finite)
    (f : ℝ → β) (R : ℝ) :
    meanFiberFunctional p hp f (fun q _ ↦ (energyBelow q.toMeasure R).toReal) ≤
      (energyBelow p.toMeasure R).toReal := by
  let : Fintype (p.map f).support :=
    (show (p.map f).support.Finite from by simpa using hp.image f).fintype
  have h := ENNReal.toReal_mono (finiteLaw_energyBelow_ne_top p hp R)
    (energyBelow_conditional_le p hp f R)
  rw [ENNReal.toReal_sum (fun (b : (p.map f).support) _ ↦ ENNReal.mul_ne_top ((p.map f).apply_ne_top b)
    (finiteLaw_energyBelow_ne_top _ (conditionalPMF_support_finite p hp f b) R))] at h
  simp only [ENNReal.toReal_mul] at h
  rw [meanFiberFunctional_eq_sum]
  exact h

end ExactOverlaps.EntropyEnergyGap
