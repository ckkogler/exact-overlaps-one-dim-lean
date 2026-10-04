module

public import ExactOverlaps.Probability.FiniteWindowError
public import ExactOverlaps.Probability.CutBlockVariance

/-!
# Contiguous blocks selected by real windows

For a monotone finite real statistic, every nonempty half-open window selects
an interval of atom indices. Its genuine measure-level local variance is the
same block error coefficient used by the cut partition.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical

namespace ExactOverlaps.Poisson

noncomputable def windowIndices {n : ℕ} (x : Fin (n + 1) → ℝ) (a r : ℝ) :
    Finset (Fin (n + 1)) := Finset.univ.filter (fun z ↦ x z ∈ Ico a (a + r))

@[simp] lemma mem_windowIndices {n : ℕ} (x : Fin (n + 1) → ℝ) (a r : ℝ)
    (z : Fin (n + 1)) : z ∈ windowIndices x a r ↔ x z ∈ Ico a (a + r) := by
  simp [windowIndices]

lemma windowIndices_between {n : ℕ} (x : Fin (n + 1) → ℝ) (hx : Monotone x)
    (a r : ℝ) {i j z : Fin (n + 1)} (hi : i ∈ windowIndices x a r)
    (hj : j ∈ windowIndices x a r) (hiz : i ≤ z) (hzj : z ≤ j) :
    z ∈ windowIndices x a r := by
  rw [mem_windowIndices] at hi hj ⊢
  exact ⟨hi.1.trans (hx hiz), (hx hzj).trans_lt hj.2⟩

lemma windowIndices_eq_Icc {n : ℕ} (x : Fin (n + 1) → ℝ) (hx : Monotone x)
    (a r : ℝ) (h : (windowIndices x a r).Nonempty) :
    windowIndices x a r = Finset.Icc ((windowIndices x a r).min' h)
      ((windowIndices x a r).max' h) := by
  ext z
  constructor
  · intro hz
    exact Finset.mem_Icc.mpr ⟨Finset.min'_le _ _ hz, Finset.le_max' _ _ hz⟩
  · intro hz
    exact windowIndices_between x hx a r (Finset.min'_mem _ _) (Finset.max'_mem _ _)
      (Finset.mem_Icc.mp hz).1 (Finset.mem_Icc.mp hz).2

/-- Selecting an index block identifies its coefficient with the actual window variance. -/
lemma localVarianceMass_of_window_block {n : ℕ} (p : PMF (Fin (n + 1)))
    (hp : p.support.Finite) (x : Fin (n + 1) → ℝ) (a r : ℝ)
    (i j : Fin (n + 1)) (h : windowIndices x a r = Finset.Icc i j) :
    VarianceEnergy.localVarianceMass (p.map x).toMeasure a r =
      ENNReal.ofReal (blockVarianceMass p hp x i j) := by
  rw [VarianceEnergy.localVarianceMass_finite_statistic p hp]
  unfold blockVarianceMass
  have hw : (fun z ↦ if x z ∈ Ico a (a + r) then (p z).toReal else 0) =
      (fun z ↦ if z ∈ Finset.Icc i j then (p z).toReal else 0) := by
    funext z
    have hz : x z ∈ Ico a (a + r) ↔ z ∈ Finset.Icc i j := by
      rw [← h, mem_windowIndices]
    simp only [hz]
  rw [hw]

lemma localVarianceMass_of_window_empty {n : ℕ} (p : PMF (Fin (n + 1)))
    (hp : p.support.Finite) (x : Fin (n + 1) → ℝ) (a r : ℝ)
    (h : windowIndices x a r = ∅) :
    VarianceEnergy.localVarianceMass (p.map x).toMeasure a r = 0 := by
  rw [VarianceEnergy.localVarianceMass_finite_statistic p hp]
  have hw : (fun z ↦ if x z ∈ Ico a (a + r) then (p z).toReal else 0) =
      (fun _ ↦ (0 : ℝ)) := by
    funext z
    have hz : x z ∉ Ico a (a + r) := by
      rw [← mem_windowIndices, h]
      simp
    simp [hz]
  rw [hw]
  simp [FiniteLaw.minimumQuadraticError, FiniteLaw.quadraticError]

end ExactOverlaps.Poisson
