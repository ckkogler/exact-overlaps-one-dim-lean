module

public import ExactOverlaps.VarianceEnergy.Measurable
public import ExactOverlaps.Probability.FiberVarianceMass
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Finite conditional-variance identification

The measure integral over a window equals its finite weighted squared error.
Its infimum is attained at the weighted mean, including null windows. Hence
the integral definition agrees with mass times the actual conditional variance.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ExactOverlaps.VarianceEnergy

/-- The Boolean observation of membership in a half-open window. -/
def intervalLabel (a r x : ℝ) : Bool := by
  classical
  exact decide (x ∈ Ico a (a + r))

lemma localQuadraticError_finite (p : PMF ℝ) (hp : p.support.Finite) (a r c : ℝ) :
    localQuadraticError p.toMeasure a r c = ENNReal.ofReal
      (FiniteLaw.quadraticError hp.toFinset
        (fun x ↦ if x ∈ Ico a (a + r) then (p x).toReal else 0) id c) := by
  classical
  have hint (g : ℝ → ℝ) : Integrable g p.toMeasure := by
    have h : IntegrableOn g p.support p.toMeasure := IntegrableOn.of_finite hp
    rwa [IntegrableOn, PMF.restrict_toMeasure_support] at h
  have hi (g : ℝ → ℝ) :
      (∫ x, g x ∂p.toMeasure) = ∑ x ∈ hp.toFinset, (p x).toReal * g x := by
    rw [PMF.integral_eq_tsum p g (hint g)]
    apply tsum_eq_sum
    intro x hx
    have hz : p x = 0 := by simpa using hx
    simp [hz]
  rw [localQuadraticError_eq_ofReal_integral, ← integral_indicator measurableSet_Ico, hi]
  congr 1
  unfold FiniteLaw.quadraticError
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x ∈ Ico a (a + r) <;> simp [hx]

lemma localVarianceMass_finite (p : PMF ℝ) (hp : p.support.Finite) (a r : ℝ) :
    localVarianceMass p.toMeasure a r = ENNReal.ofReal
      (FiniteLaw.minimumQuadraticError hp.toFinset
        (fun x ↦ if x ∈ Ico a (a + r) then (p x).toReal else 0) id) := by
  classical
  let w : ℝ → ℝ := fun x ↦ if x ∈ Ico a (a + r) then (p x).toReal else 0
  have hw : ∀ x ∈ hp.toFinset, 0 ≤ w x := by
    intro x _
    dsimp [w]
    split_ifs <;> positivity
  apply le_antisymm
  · apply (localVarianceMass_le p.toMeasure a r
      (FiniteLaw.weightedMean hp.toFinset w id)).trans
    rw [localQuadraticError_finite p hp]
    exact le_rfl
  · apply le_iInf
    intro c
    rw [localQuadraticError_finite p hp]
    exact ENNReal.ofReal_le_ofReal (FiniteLaw.minimumQuadraticError_le hp.toFinset w id hw c)

lemma localVarianceMass_eq_fiberVarianceMass (p : PMF ℝ) (hp : p.support.Finite)
    (a r : ℝ) : localVarianceMass p.toMeasure a r =
      ENNReal.ofReal (FiniteProbability.fiberVarianceMass p hp (intervalLabel a r) id true) := by
  classical
  rw [localVarianceMass_finite p hp]
  simp only [FiniteProbability.fiberVarianceMass, intervalLabel, decide_eq_true_eq]

/-- Identification includes null windows through the zero-mass convention. -/
lemma localVarianceMass_eq_mass_mul (p : PMF ℝ) (hp : p.support.Finite) (a r : ℝ) :
    localVarianceMass p.toMeasure a r = ENNReal.ofReal
      (((p.map (intervalLabel a r)) true).toReal *
        FiniteProbability.fiberVariance p hp (intervalLabel a r) id true) := by
  rw [localVarianceMass_eq_fiberVarianceMass p hp,
    FiniteProbability.fiberVarianceMass_eq_mass_mul]

/-- On positive windows the conditional law is the normalized restriction, as a PMF. -/
lemma localVarianceMass_eq_conditional (p : PMF ℝ) (hp : p.support.Finite) (a r : ℝ)
    (h : true ∈ (p.map (intervalLabel a r)).support) :
    localVarianceMass p.toMeasure a r = ENNReal.ofReal
      (((p.map (intervalLabel a r)) true).toReal *
        FiniteProbability.variance (Entropy.conditionalPMF p (intervalLabel a r) ⟨true, h⟩)
          (Entropy.conditionalPMF_support_finite p hp (intervalLabel a r) ⟨true, h⟩) id) := by
  rw [localVarianceMass_eq_fiberVarianceMass p hp]
  congr 1
  exact FiniteProbability.fiberVarianceMass_eq_conditional p hp (intervalLabel a r) id ⟨true, h⟩

end ExactOverlaps.VarianceEnergy
