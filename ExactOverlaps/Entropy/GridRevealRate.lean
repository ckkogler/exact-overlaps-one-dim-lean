module

public import ExactOverlaps.Entropy.GridCellRate
public import ExactOverlaps.Entropy.CutRevealIntegral
public import ExactOverlaps.Probability.ProductCutAverage
public import ExactOverlaps.Probability.GridGeometry

/-!
# The entropy reveal rate is bounded by marginal Poisson dispersions

At each actual cut state, all inactive gap increments are bounded by the
conditional-cell estimate. Averaging the independent cut families reduces
each coordinate term to its genuine one-dimensional Poisson dispersion.
-/

@[expose] public section

open scoped BigOperators Classical
open ExactOverlaps.Poisson ExactOverlaps.FiniteProbability

namespace ExactOverlaps.Entropy

lemma averageStatisticConditionalEntropy_nonneg {α β γ : Type*}
    (p : PMF α) (hp : p.support.Finite) (s : α → β) (g : α → γ) :
    0 ≤ averageStatisticConditionalEntropy p hp s g := by
  unfold averageStatisticConditionalEntropy
  exact Finset.sum_nonneg (fun _ _ ↦ mul_nonneg ENNReal.toReal_nonneg (finiteEntropy_nonneg _ _))

lemma grid_inactive_increments_le {m n : ℕ} (p : Fin m → PMF (Fin (n + 1)))
    (hp : ∀ i, (p i).support.Finite) (x : ℕ → ℝ)
    (hx : Monotone (fun k : Fin (n + 1) ↦ x k.val)) (c : Fin m × Fin n → Bool) :
    (∑ ij : Fin m × Fin n, if c ij then 0 else orderedGapLength x n ij.2 *
      averageStatisticConditionalEntropy (tupleLaw m p) (tupleLaw_support_finite m p hp)
        (fun w ↦ (tupleSum (fun k : Fin (n + 1) ↦ x k.val) m w,
          cutLabel (tupleGridSide m n) c w)) (tupleGridSide m n ij)) ≤
      9 * m * ∑ i, cellDispersion (p i) (hp i) x (fun j ↦ c (i, j)) := by
  calc
    _ ≤ ∑ ij : Fin m × Fin n, orderedGapLength x n ij.2 *
        averageStatisticConditionalEntropy (tupleLaw m p) (tupleLaw_support_finite m p hp)
          (fun w ↦ (tupleSum (fun k : Fin (n + 1) ↦ x k.val) m w,
            cutLabel (tupleGridSide m n) c w)) (tupleGridSide m n ij) := by
      apply Finset.sum_le_sum
      intro ij _
      split_ifs
      · exact mul_nonneg (orderedGapLength_nonneg x n (grid_monotoneOn x hx) ij.2)
          (averageStatisticConditionalEntropy_nonneg _ _ _ _)
      · exact le_rfl
    _ = meanFiberFunctional (tupleLaw m p) (tupleLaw_support_finite m p hp)
        (cutLabel (tupleGridSide m n) c) (fun q hq ↦ gridCellCutEntropy q hq x) := by
      rw [mean_gridCellCutEntropy_eq, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      exact averageStatisticConditionalEntropy_condition_swap
        (tupleLaw m p) (tupleLaw_support_finite m p hp)
        (tupleSum (fun k : Fin (n + 1) ↦ x k.val) m)
        (cutLabel (tupleGridSide m n) c) (tupleGridSide m n (i, j))
    _ ≤ _ := mean_gridCellCutEntropy_le p hp x hx c

theorem grid_revealedEntropyRate_le {m n : ℕ} (p : Fin m → PMF (Fin (n + 1)))
    (hp : ∀ i, (p i).support.Finite) (x : ℕ → ℝ)
    (hx : Monotone (fun k : Fin (n + 1) ↦ x k.val)) {t : ℝ} (ht : 0 ≤ t) :
    revealedEntropyRate (tupleLaw m p) (tupleLaw_support_finite m p hp)
      (tupleSum (fun k : Fin (n + 1) ↦ x k.val) m) (tupleGridSide m n)
      (fun ij ↦ orderedGapLength x n ij.2) t ≤
      9 * m * ∑ i, cutDispersion (p i) (hp i) x t := by
  unfold revealedEntropyRate
  calc
    _ ≤ ∑ c : Fin m × Fin n → Bool, cutWeight (fun ij ↦ orderedGapLength x n ij.2) t c *
        (9 * m * ∑ i, cellDispersion (p i) (hp i) x (fun j ↦ c (i, j))) := by
      have h (c : Fin m × Fin n → Bool) :=
        mul_le_mul_of_nonneg_left (grid_inactive_increments_le p hp x hx c)
          (cutWeight_nonneg _ (fun ij ↦ orderedGapLength_nonneg x n (grid_monotoneOn x hx) ij.2) ht c)
      convert Finset.sum_le_sum (s := Finset.univ) (fun c _ ↦ h c) using 1
      congr 1
      ext
      simp
    _ = 9 * m * ∑ c : Fin m × Fin n → Bool, ∑ i,
        cutWeight (fun ij ↦ orderedGapLength x n ij.2) t c *
          cellDispersion (p i) (hp i) x (fun j ↦ c (i, j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      rw [← Finset.mul_sum]
      ring
    _ = 9 * m * ∑ i, ∑ c : Fin m × Fin n → Bool,
        cutWeight (fun ij ↦ orderedGapLength x n ij.2) t c *
          cellDispersion (p i) (hp i) x (fun j ↦ c (i, j)) := by rw [Finset.sum_comm]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      unfold cutDispersion
      convert sum_cutWeight_coordinate (fun ij ↦ orderedGapLength x n ij.2) t i
        (cellDispersion (p i) (hp i) x) using 1 <;> congr 1 <;> ext <;> simp

end ExactOverlaps.Entropy
