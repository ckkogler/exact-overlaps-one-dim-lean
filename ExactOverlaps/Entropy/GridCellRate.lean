module

public import ExactOverlaps.Entropy.TupleGridEntropyBound
public import ExactOverlaps.Entropy.FiberEntropyAverage
public import ExactOverlaps.Probability.ProductCellDispersion

/-!
# Averaging the grid entropy estimate over actual rectangular cells

The conditional entropy tower moves the sum statistic inside each observed
cell. Exact rectangular conditioning permits the tuple cumulative-entropy
bound there, and marginal averaging gives the sum of genuine cell dispersions.
-/

@[expose] public section

open scoped BigOperators Classical
open ExactOverlaps.Poisson ExactOverlaps.FiniteLaw ExactOverlaps.FiniteProbability

namespace ExactOverlaps.Entropy

noncomputable def gridCellCutEntropy {m n : ℕ} (p : PMF (FiniteTuple (Fin (n + 1)) m))
    (hp : p.support.Finite) (x : ℕ → ℝ) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin n, (x (j.val + 1) - x j.val) *
    averageStatisticConditionalEntropy p hp (tupleSum (fun k : Fin (n + 1) ↦ x k.val) m)
      (fun w ↦ decide (j.val < (tupleCoordinate m w i).val))

noncomputable def gridCoordinateDispersionSum {m n : ℕ} (p : PMF (FiniteTuple (Fin (n + 1)) m))
    (hp : p.support.Finite) (x : ℕ → ℝ) : ℝ :=
  ∑ i : Fin m, dispersion p hp (fun w ↦ x (tupleCoordinate m w i).val)

lemma gridCellCutEntropy_le_product {m n : ℕ} (p : Fin m → PMF (Fin (n + 1)))
    (hp : ∀ i, (p i).support.Finite) (x : ℕ → ℝ)
    (hx : Monotone (fun k : Fin (n + 1) ↦ x k.val)) :
    gridCellCutEntropy (tupleLaw m p) (tupleLaw_support_finite m p hp) x ≤
      9 * m * gridCoordinateDispersionSum (tupleLaw m p) (tupleLaw_support_finite m p hp) x := by
  have he : gridCoordinateDispersionSum (tupleLaw m p) (tupleLaw_support_finite m p hp) x =
      ∑ i, dispersion (p i) (hp i) (fun a ↦ x a.val) := by
    unfold gridCoordinateDispersionSum
    apply Finset.sum_congr rfl
    intro i _
    exact dispersion_tupleCoordinate (fun a : Fin (n + 1) ↦ x a.val) m p hp i
  rw [he]
  exact sum_all_grid_tuple_cut_entropy_le p hp x hx

lemma mean_gridCellCutEntropy_eq {m n : ℕ} (p : PMF (FiniteTuple (Fin (n + 1)) m))
    (hp : p.support.Finite) (x : ℕ → ℝ) (c : Fin m × Fin n → Bool) :
    meanFiberFunctional p hp (cutLabel (tupleGridSide m n) c)
      (fun q hq ↦ gridCellCutEntropy q hq x) =
    ∑ i : Fin m, ∑ j : Fin n, (x (j.val + 1) - x j.val) *
      averageStatisticConditionalEntropy p hp
        (fun w ↦ (cutLabel (tupleGridSide m n) c w, tupleSum (fun k : Fin (n + 1) ↦ x k.val) m w))
        (fun w ↦ decide (j.val < (tupleCoordinate m w i).val)) := by
  unfold gridCellCutEntropy
  simp_rw [meanFiberFunctional_sum, meanFiberFunctional_const_mul,
    meanFiberFunctional_conditionalEntropy]

lemma mean_gridCoordinateDispersionSum_eq {m n : ℕ} (p : Fin m → PMF (Fin (n + 1)))
    (hp : ∀ i, (p i).support.Finite) (x : ℕ → ℝ) (c : Fin m × Fin n → Bool) :
    meanFiberFunctional (tupleLaw m p) (tupleLaw_support_finite m p hp)
      (cutLabel (tupleGridSide m n) c) (fun q hq ↦ gridCoordinateDispersionSum q hq x) =
      ∑ i : Fin m, cellDispersion (p i) (hp i) x (fun j ↦ c (i, j)) := by
  unfold gridCoordinateDispersionSum
  rw [meanFiberFunctional_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact meanFiberFunctional_tupleGrid_dispersion p hp x c i

lemma gridCellCutEntropy_conditional_le {m n : ℕ} (p : Fin m → PMF (Fin (n + 1)))
    (hp : ∀ i, (p i).support.Finite) (x : ℕ → ℝ)
    (hx : Monotone (fun k : Fin (n + 1) ↦ x k.val)) (c : Fin m × Fin n → Bool)
    (b : ((tupleLaw m p).map (cutLabel (tupleGridSide m n) c)).support) :
    gridCellCutEntropy (conditionalPMF (tupleLaw m p) (cutLabel (tupleGridSide m n) c) b)
      (conditionalPMF_support_finite _ (tupleLaw_support_finite m p hp) _ b) x ≤
    9 * m * gridCoordinateDispersionSum
      (conditionalPMF (tupleLaw m p) (cutLabel (tupleGridSide m n) c) b)
      (conditionalPMF_support_finite _ (tupleLaw_support_finite m p hp) _ b) x := by
  obtain ⟨a, ha, hab⟩ := (PMF.mem_support_map_iff (cutLabel (tupleGridSide m n) c) (tupleLaw m p) b.val).mp b.property
  let w : (tupleLaw m p).support := ⟨a, ha⟩
  let μ (i : Fin m) := conditionalAt (p i) (cutLabel (indexSide n) (fun j ↦ c (i, j)))
    (tupleSupportCoordinate m p w i)
  have hμ (i : Fin m) : (μ i).support.Finite := conditionalPMF_support_finite (p i) (hp i) _ _
  have hq : conditionalPMF (tupleLaw m p) (cutLabel (tupleGridSide m n) c) b = tupleLaw m μ := by
    apply Eq.trans _ (conditionalAt_tupleGridCut p c w)
    unfold conditionalAt
    apply congrArg (conditionalPMF (tupleLaw m p) (cutLabel (tupleGridSide m n) c))
    exact Subtype.ext hab.symm
  rw [finiteFunctional_congr (fun q hq ↦ gridCellCutEntropy q hq x) hq _ (tupleLaw_support_finite m μ hμ),
    finiteFunctional_congr (fun q hq ↦ gridCoordinateDispersionSum q hq x) hq _
      (tupleLaw_support_finite m μ hμ)]
  exact gridCellCutEntropy_le_product μ hμ x hx

theorem mean_gridCellCutEntropy_le {m n : ℕ} (p : Fin m → PMF (Fin (n + 1)))
    (hp : ∀ i, (p i).support.Finite) (x : ℕ → ℝ)
    (hx : Monotone (fun k : Fin (n + 1) ↦ x k.val)) (c : Fin m × Fin n → Bool) :
    meanFiberFunctional (tupleLaw m p) (tupleLaw_support_finite m p hp)
      (cutLabel (tupleGridSide m n) c) (fun q hq ↦ gridCellCutEntropy q hq x) ≤
      9 * m * ∑ i, cellDispersion (p i) (hp i) x (fun j ↦ c (i, j)) := by
  have h := meanFiberFunctional_mono (tupleLaw m p) (tupleLaw_support_finite m p hp)
    (cutLabel (tupleGridSide m n) c)
    (fun q hq ↦ gridCellCutEntropy q hq x)
    (fun q hq ↦ 9 * m * gridCoordinateDispersionSum q hq x)
    (gridCellCutEntropy_conditional_le p hp x hx c)
  rw [meanFiberFunctional_const_mul, mean_gridCoordinateDispersionSum_eq] at h
  exact h

end ExactOverlaps.Entropy
