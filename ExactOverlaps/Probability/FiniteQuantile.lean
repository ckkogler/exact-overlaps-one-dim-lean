module

public import ExactOverlaps.Entropy.CrossEntropy

/-!
# Finite cumulative square-root estimates

If each value dominates the mass accumulated up to its index, its weighted
inverse square-root average is bounded by twice the square root of total
mass. The same argument applies after restricting to the strict lower half.
-/

@[expose] public section

open scoped BigOperators Classical

namespace ExactOverlaps.FiniteProbability

lemma sum_div_sqrt_le_of_cumulative_le (w z : ℕ → ℝ) (n : ℕ)
    (hw : ∀ i < n, 0 ≤ w i)
    (hz : ∀ i < n, (∑ j ∈ Finset.range (i + 1), w j) ≤ z i) :
    (∑ i ∈ Finset.range n, w i / Real.sqrt (z i)) ≤
      2 * Real.sqrt (∑ i ∈ Finset.range n, w i) := by
  apply le_trans _ (Entropy.sum_div_sqrt_cumulative_le w n hw)
  apply Finset.sum_le_sum
  intro i hi
  have hin : i < n := Finset.mem_range.mp hi
  have hwi := hw i hin
  have hcum : 0 ≤ ∑ j ∈ Finset.range (i + 1), w j := by
    apply Finset.sum_nonneg
    intro j hj
    exact hw j (by have hj' := Finset.mem_range.mp hj; omega)
  have hweight : w i ≤ ∑ j ∈ Finset.range (i + 1), w j := by
    apply Finset.single_le_sum
    · intro j hj
      exact hw j (by have hj' := Finset.mem_range.mp hj; omega)
    · exact Finset.mem_range.mpr (Nat.lt_succ_self i)
  by_cases hc : (∑ j ∈ Finset.range (i + 1), w j) = 0
  · have hzero : w i = 0 := by linarith
    simp [hzero]
  · have hpos : 0 < ∑ j ∈ Finset.range (i + 1), w j := lt_of_le_of_ne hcum (Ne.symm hc)
    exact div_le_div_of_nonneg_left hwi (Real.sqrt_pos.mpr hpos) (Real.sqrt_le_sqrt (hz i hin))

lemma sum_lower_half_div_sqrt_le (w z : ℕ → ℝ) (n : ℕ)
    (hw : ∀ i < n, 0 ≤ w i)
    (hz : ∀ i < n, (∑ j ∈ Finset.range (i + 1), w j) ≤ z i) :
    (∑ i ∈ Finset.range n, if z i < 1 / 2 then w i / Real.sqrt (z i) else 0) ≤
      2 * Real.sqrt (∑ i ∈ Finset.range n, if z i < 1 / 2 then w i else 0) := by
  let v (i : ℕ) := if z i < 1 / 2 then w i else 0
  have hv : ∀ i < n, 0 ≤ v i := by
    intro i hi
    dsimp [v]
    split_ifs
    · exact hw i hi
    · exact le_rfl
  have hvcum : ∀ i < n, (∑ j ∈ Finset.range (i + 1), v j) ≤ z i := by
    intro i hi
    apply le_trans _ (hz i hi)
    apply Finset.sum_le_sum
    intro j hj
    have hjn : j < n := by have hj' := Finset.mem_range.mp hj; omega
    dsimp [v]
    split_ifs
    · exact le_rfl
    · exact hw j hjn
  have h := sum_div_sqrt_le_of_cumulative_le v z n hv hvcum
  have he : (∑ i ∈ Finset.range n, if z i < 1 / 2 then w i / Real.sqrt (z i) else 0) =
      ∑ i ∈ Finset.range n, v i / Real.sqrt (z i) := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp [v]
    split_ifs <;> simp
  rw [he]
  exact h

end ExactOverlaps.FiniteProbability
