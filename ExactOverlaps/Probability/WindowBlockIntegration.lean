module

public import ExactOverlaps.Probability.WindowBlockGeometry
public import ExactOverlaps.Probability.WindowBlockSum

/-!
# Integrating the exact window block expansion

The genuine local variance integral is the finite sum of each block error
times the Lebesgue measure of origins selecting that block.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical

namespace ExactOverlaps.Poisson

lemma measurableSet_windowOrigins {n : ℕ} (x : Fin (n + 1) → ℝ) (r : ℝ)
    (i j : Fin (n + 1)) : MeasurableSet (windowOrigins x r i j) := by
  have hm (z : Fin (n + 1)) : MeasurableSet {a : ℝ | x z ∈ Ico a (a + r)} :=
    (measurableSet_le measurable_id measurable_const).inter
      (measurableSet_lt measurable_const (measurable_id.add_const r))
  have he : windowOrigins x r i j =
      ⋂ z : Fin (n + 1), {a : ℝ | (x z ∈ Ico a (a + r)) ↔ z ∈ Finset.Icc i j} := by
    ext a
    simp only [windowOrigins, mem_ofPred_eq, mem_iInter, Finset.ext_iff, mem_windowIndices]
  rw [he]
  apply MeasurableSet.iInter
  intro z
  by_cases hz : z ∈ Finset.Icc i j
  · simpa only [hz, iff_true] using hm z
  · simp only [hz, iff_false]
    exact (hm z).compl

lemma lintegral_localVarianceMass_eq_blocks {n : ℕ} (p : PMF (Fin (n + 1)))
    (hp : p.support.Finite) (x : Fin (n + 1) → ℝ) (hx : Monotone x) (r : ℝ) :
    (∫⁻ a : ℝ, VarianceEnergy.localVarianceMass (p.map x).toMeasure a r) =
      ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), if i ≤ j then
        ENNReal.ofReal (blockVarianceMass p hp x i j) * volume (windowOrigins x r i j)
        else 0 := by
  let f (i j : Fin (n + 1)) : ℝ → ℝ≥0∞ :=
    if i ≤ j then (windowOrigins x r i j).indicator
      (fun _ ↦ ENNReal.ofReal (blockVarianceMass p hp x i j)) else fun _ ↦ 0
  have hm (i j : Fin (n + 1)) : Measurable (f i j) := by
    dsimp [f]
    split_ifs
    · exact measurable_const.indicator (measurableSet_windowOrigins x r i j)
    · exact measurable_const
  have he (a : ℝ) : VarianceEnergy.localVarianceMass (p.map x).toMeasure a r =
      ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), f i j a := by
    rw [localVarianceMass_eq_block_sum p hp x hx a r]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i ≤ j <;> simp [f, hij, windowOrigins, Set.indicator]
  simp_rw [he]
  rw [lintegral_finsetSum _ (fun i _ ↦ Finset.measurable_sum _ (fun j _ ↦ hm i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [lintegral_finsetSum _ (fun j _ ↦ hm i j)]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i ≤ j
  · simp only [f, hij, ite_true]
    exact lintegral_indicator_const (measurableSet_windowOrigins x r i j) _
  · simp [f, hij]

end ExactOverlaps.Poisson
