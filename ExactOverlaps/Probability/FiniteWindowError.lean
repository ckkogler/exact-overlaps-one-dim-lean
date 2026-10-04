module

public import ExactOverlaps.VarianceEnergy.FiniteLawBridge

/-!
# Window error of a finite real statistic

The measure-level window error of a mapped finite law is the finite quadratic
error over its original atoms. Coincident statistic values and null atoms are
allowed; no injectivity hypothesis is needed.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical

namespace ExactOverlaps.VarianceEnergy

lemma quadraticError_window_eq_sum {α : Type*} (s : Finset α) (w g : α → ℝ)
    (a r c : ℝ) :
    FiniteLaw.quadraticError s (fun z ↦ if g z ∈ Ico a (a + r) then w z else 0) g c =
      ∑ z ∈ s, w z * (if g z ∈ Ico a (a + r) then (g z - c) ^ 2 else 0) := by
  unfold FiniteLaw.quadraticError
  apply Finset.sum_congr rfl
  intro z _
  split_ifs with hz <;> simp [hz]

lemma localQuadraticError_finite_statistic {α : Type*} (p : PMF α)
    (hp : p.support.Finite) (g : α → ℝ) (a r c : ℝ) :
    localQuadraticError (p.map g).toMeasure a r c = ENNReal.ofReal
      (FiniteLaw.quadraticError hp.toFinset
        (fun z ↦ if g z ∈ Ico a (a + r) then (p z).toReal else 0) g c) := by
  let hq : (p.map g).support.Finite := by simpa using hp.image g
  rw [localQuadraticError_finite (p.map g) hq]
  congr 1
  calc
    _ = ∑ y ∈ hq.toFinset, ((p.map g) y).toReal *
        (if y ∈ Ico a (a + r) then (y - c) ^ 2 else 0) := by
      unfold FiniteLaw.quadraticError
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : y ∈ Ico a (a + r) <;> simp [hy]
    _ = ∑ z ∈ hp.toFinset, (p z).toReal *
        (if g z ∈ Ico a (a + r) then (g z - c) ^ 2 else 0) :=
      Entropy.sum_marginal_mul p hp g (fun y ↦ if y ∈ Ico a (a + r) then (y - c) ^ 2 else 0)
    _ = _ := (quadraticError_window_eq_sum hp.toFinset (fun z ↦ (p z).toReal) g a r c).symm

/-- The indexed finite quadratic minimum equals the genuine local variance of the mapped law. -/
lemma localVarianceMass_finite_statistic {α : Type*} (p : PMF α)
    (hp : p.support.Finite) (g : α → ℝ) (a r : ℝ) :
    localVarianceMass (p.map g).toMeasure a r = ENNReal.ofReal
      (FiniteLaw.minimumQuadraticError hp.toFinset
        (fun z ↦ if g z ∈ Ico a (a + r) then (p z).toReal else 0) g) := by
  let w : α → ℝ := fun z ↦ if g z ∈ Ico a (a + r) then (p z).toReal else 0
  have hw : ∀ z ∈ hp.toFinset, 0 ≤ w z := by
    intro z _
    dsimp [w]
    split_ifs <;> positivity
  apply le_antisymm
  · apply (localVarianceMass_le (p.map g).toMeasure a r
      (FiniteLaw.weightedMean hp.toFinset w g)).trans
    rw [localQuadraticError_finite_statistic p hp]
    exact le_rfl
  · apply le_iInf
    intro c
    rw [localQuadraticError_finite_statistic p hp]
    exact ENNReal.ofReal_le_ofReal (FiniteLaw.minimumQuadraticError_le hp.toFinset w g hw c)

end ExactOverlaps.VarianceEnergy
