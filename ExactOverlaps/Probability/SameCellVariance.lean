module

public import ExactOverlaps.Probability.FiberVarianceMass

/-!
# Independent-copy square distances inside observation cells

The unnormalized independent-copy contribution of a fiber is at most twice
its variance mass. Summing over the observation gives twice the mean of the
actual conditional variances, including all null fibers without exceptions.
-/

@[expose] public section

open scoped BigOperators ENNReal Classical

namespace ExactOverlaps.FiniteProbability

lemma sum_fiberVarianceMass {α β : Type*} [Fintype β] (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (g : α → ℝ) :
    (∑ b : β, fiberVarianceMass p hp f g b) = meanConditionalVariance p hp f g := by
  simp_rw [fiberVarianceMass_eq_mass_mul, ← sum_fiber_weights p hp f, Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold meanConditionalVariance expectation
  apply Finset.sum_congr rfl
  intro a _
  simp [ite_mul]

/-- Independent-copy square distance retained only when the observations agree. -/
noncomputable def sameCellSquareDistance {α β : Type*} [DecidableEq β] (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (g : α → ℝ) : ℝ :=
  ∑ a ∈ hp.toFinset, ∑ b ∈ hp.toFinset,
    if f a = f b then (p a).toReal * (p b).toReal * (g a - g b) ^ 2 else 0

lemma sameCellSquareDistance_eq_sum_fibers {α β : Type*} [Fintype β] (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (g : α → ℝ) :
    sameCellSquareDistance p hp f g =
      ∑ z : β, ∑ a ∈ hp.toFinset, ∑ b ∈ hp.toFinset,
        (if f a = z then (p a).toReal else 0) *
          (if f b = z then (p b).toReal else 0) * (g a - g b) ^ 2 := by
  unfold sameCellSquareDistance
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_eq_single (f a)]
  · by_cases h : f a = f b <;> simp [h, Ne.symm]
  · intro z _ hz
    simp [Ne.symm hz]
  · simp

/-- The finite version of the same-cell independent-copy bound. -/
theorem sameCellSquareDistance_le {α β : Type*} [Fintype β] (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (g : α → ℝ) :
    sameCellSquareDistance p hp f g ≤ 2 * meanConditionalVariance p hp f g := by
  rw [sameCellSquareDistance_eq_sum_fibers, ← sum_fiberVarianceMass, Finset.mul_sum]
  exact Finset.sum_le_sum (fun z _ ↦ pairwise_same_fiber_sq_le p hp f g z)

end ExactOverlaps.FiniteProbability
