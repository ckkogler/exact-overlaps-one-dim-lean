module

public import ExactOverlaps.Probability.CutBlockLabels
public import ExactOverlaps.Probability.VarianceRefinement

/-!
# Variance as a finite sum over contiguous cells

Relabeling cells by their endpoint indices expresses the mean conditional
variance as the sum of the unnormalized quadratic errors of those blocks
selected by the cut pattern. No assumption on individual atom masses occurs.
-/

@[expose] public section

open scoped BigOperators ENNReal Classical

namespace ExactOverlaps.Poisson

noncomputable def blockVarianceMass {n : ℕ} (p : PMF (Fin (n + 1)))
    (hp : p.support.Finite) (x : Fin (n + 1) → ℝ) (a b : Fin (n + 1)) : ℝ :=
  FiniteLaw.minimumQuadraticError hp.toFinset
    (fun z ↦ if z ∈ Finset.Icc a b then (p z).toReal else 0) x

lemma blockVarianceMass_nonneg {n : ℕ} (p : PMF (Fin (n + 1)))
    (hp : p.support.Finite) (x : Fin (n + 1) → ℝ) (a b : Fin (n + 1)) :
    0 ≤ blockVarianceMass p hp x a b := by
  apply FiniteLaw.minimumQuadraticError_nonneg
  intro z _
  split_ifs <;> positivity

lemma fiberVarianceMass_cellEndpoints {n : ℕ} (p : PMF (Fin (n + 1)))
    (hp : p.support.Finite) (x : Fin (n + 1) → ℝ) (c : Fin n → Bool)
    (a b : Fin (n + 1)) :
    FiniteProbability.fiberVarianceMass p hp (cellEndpoints c) x (a, b) =
      if blockPattern c a b then blockVarianceMass p hp x a b else 0 := by
  unfold FiniteProbability.fiberVarianceMass
  by_cases h : blockPattern c a b
  · rw [ite_eq_left h]
    unfold blockVarianceMass
    congr 1
    funext z
    simp only [cellEndpoints_eq_pair_iff, h, true_and]
  · rw [ite_eq_right h]
    have hw : (fun z ↦ if cellEndpoints c z = (a, b) then (p z).toReal else 0) =
        (fun _ ↦ (0 : ℝ)) := by
      funext z
      simp [cellEndpoints_eq_pair_iff, h]
    rw [hw]
    simp [FiniteLaw.minimumQuadraticError, FiniteLaw.quadraticError]

lemma meanConditionalVariance_eq_blocks {n : ℕ} (p : PMF (Fin (n + 1)))
    (hp : p.support.Finite) (x : Fin (n + 1) → ℝ) (c : Fin n → Bool) :
    FiniteProbability.meanConditionalVariance p hp (cutLabel (indexSide n) c) x =
      ∑ a : Fin (n + 1), ∑ b : Fin (n + 1),
        if blockPattern c a b then blockVarianceMass p hp x a b else 0 := by
  have he : FiniteProbability.meanConditionalVariance p hp (cutLabel (indexSide n) c) x =
      FiniteProbability.meanConditionalVariance p hp (cellEndpoints c) x := by
    apply FiniteProbability.meanConditionalVariance_congr_fibers
    intro a b
    exact (cellEndpoints_eq_iff c a b).symm
  rw [he]
  have hsum : FiniteProbability.meanConditionalVariance p hp (cellEndpoints c) x =
      ∑ z : Fin (n + 1) × Fin (n + 1),
        FiniteProbability.fiberVarianceMass p hp (cellEndpoints c) x z := by
    convert (FiniteProbability.sum_fiberVarianceMass p hp (cellEndpoints c) x).symm using 1 <;>
      congr 3
    funext z
    congr 1
  rw [hsum, Fintype.sum_prod_type]
  simp_rw [fiberVarianceMass_cellEndpoints]

/-- Real probability weight of the actual event selecting a specified contiguous cell. -/
noncomputable def blockWeight {n : ℕ} (d : Fin n → ℝ) (t : ℝ)
    (a b : Fin (n + 1)) : ℝ :=
  ∑ c : Fin n → Bool, if blockPattern c a b then cutWeight d t c else 0

lemma cutVariance_eq_blocks {n : ℕ} (p : PMF (Fin (n + 1)))
    (hp : p.support.Finite) (x : ℕ → ℝ) (t : ℝ) :
    cutVariance p hp x t = ∑ a : Fin (n + 1), ∑ b : Fin (n + 1),
      blockVarianceMass p hp (fun z ↦ x z.val) a b * blockWeight (orderedGapLength x n) t a b := by
  unfold cutVariance
  simp_rw [meanConditionalVariance_eq_blocks, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  unfold blockWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs <;> ring

lemma blockVarianceMass_singleton {n : ℕ} (p : PMF (Fin (n + 1)))
    (hp : p.support.Finite) (x : Fin (n + 1) → ℝ) (a : Fin (n + 1)) :
    blockVarianceMass p hp x a a = 0 := by
  apply le_antisymm _ (blockVarianceMass_nonneg p hp x a a)
  apply (FiniteLaw.minimumQuadraticError_le hp.toFinset
    (fun z ↦ if z ∈ Finset.Icc a a then (p z).toReal else 0) x
    (fun z _ ↦ by split_ifs <;> positivity) (x a)).trans
  apply le_of_eq
  unfold FiniteLaw.quadraticError
  apply Finset.sum_eq_zero
  intro z _
  by_cases hz : z = a <;> simp [hz]

end ExactOverlaps.Poisson
