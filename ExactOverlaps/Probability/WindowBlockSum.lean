module

public import ExactOverlaps.Probability.WindowBlocks

/-!
# Exact finite block expansion of local variance

Every nonempty ordered window has unique block endpoints. Empty windows
contribute zero, so the local variance is a finite sum of block coefficients.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical

namespace ExactOverlaps.Poisson

lemma finset_Icc_endpoints_eq {n : ℕ} (i j k l : Fin (n + 1))
    (hij : i ≤ j) (hkl : k ≤ l) (h : Finset.Icc i j = Finset.Icc k l) :
    i = k ∧ j = l := by
  have hi : i ∈ Finset.Icc k l := by rw [← h]; exact Finset.mem_Icc.mpr ⟨le_rfl, hij⟩
  have hj : j ∈ Finset.Icc k l := by rw [← h]; exact Finset.mem_Icc.mpr ⟨hij, le_rfl⟩
  have hk : k ∈ Finset.Icc i j := by rw [h]; exact Finset.mem_Icc.mpr ⟨le_rfl, hkl⟩
  have hl : l ∈ Finset.Icc i j := by rw [h]; exact Finset.mem_Icc.mpr ⟨hkl, le_rfl⟩
  exact ⟨le_antisymm (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hi).1,
    le_antisymm (Finset.mem_Icc.mp hj).2 (Finset.mem_Icc.mp hl).2⟩

lemma localVarianceMass_eq_block_sum {n : ℕ} (p : PMF (Fin (n + 1)))
    (hp : p.support.Finite) (x : Fin (n + 1) → ℝ) (hx : Monotone x) (a r : ℝ) :
    VarianceEnergy.localVarianceMass (p.map x).toMeasure a r =
      ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
        if i ≤ j ∧ windowIndices x a r = Finset.Icc i j then
          ENNReal.ofReal (blockVarianceMass p hp x i j) else 0 := by
  by_cases hn : (windowIndices x a r).Nonempty
  · let i := (windowIndices x a r).min' hn
    let j := (windowIndices x a r).max' hn
    have hij : i ≤ j := Finset.min'_le _ _ (Finset.max'_mem _ _)
    have he : windowIndices x a r = Finset.Icc i j := windowIndices_eq_Icc x hx a r hn
    have hiff (k l : Fin (n + 1)) :
        (k ≤ l ∧ windowIndices x a r = Finset.Icc k l) ↔ k = i ∧ l = j := by
      constructor
      · rintro ⟨hkl, h⟩
        exact finset_Icc_endpoints_eq k l i j hkl hij (h.symm.trans he)
      · rintro ⟨rfl, rfl⟩
        exact ⟨hij, he⟩
    simp_rw [hiff]
    simpa only [ite_and, Finset.sum_ite_irrel, Finset.sum_ite_eq',
      Finset.mem_univ, ite_eq_left_iff, Finset.sum_const_zero, ite_true] using
      localVarianceMass_of_window_block p hp x a r i j he
  · have he : windowIndices x a r = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    rw [localVarianceMass_of_window_empty p hp x a r he]
    symm
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    rw [ite_eq_right]
    rintro ⟨hij, h⟩
    have hi : i ∈ windowIndices x a r := by rw [h]; exact Finset.mem_Icc.mpr ⟨le_rfl, hij⟩
    rw [he] at hi
    exact Finset.notMem_empty _ hi

end ExactOverlaps.Poisson
