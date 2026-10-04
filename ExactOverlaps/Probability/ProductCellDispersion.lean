module

public import ExactOverlaps.Probability.ProductCutCells
public import ExactOverlaps.Probability.FiberAverages
public import ExactOverlaps.Probability.FiniteProductDispersion
public import ExactOverlaps.Probability.ConditionalDispersion

/-!
# Marginal dispersion averaged over rectangular cut cells

Inside an actual rectangular cell the conditional law is a product. Its
coordinate dispersion is therefore the genuine marginal cell dispersion.
Averaging over the whole tuple reduces to averaging that coordinate's
original law, with all null atoms ignored by their zero probability.
-/

@[expose] public section

open scoped BigOperators Classical
open ExactOverlaps.Entropy ExactOverlaps.FiniteProbability ExactOverlaps.FiniteLaw

namespace ExactOverlaps.Poisson

lemma cellDispersion_eq_meanFiberFunctional {n : ℕ} (p : PMF (Fin (n + 1)))
    (hp : p.support.Finite) (x : ℕ → ℝ) (c : Fin n → Bool) :
    cellDispersion p hp x c = meanFiberFunctional p hp (cutLabel (indexSide n) c)
      (fun q hq ↦ dispersion q hq (fun a : Fin (n + 1) ↦ x a.val)) := by
  rw [meanFiberFunctional_eq_sum]
  rfl

lemma fiberFunctional_tupleGrid_dispersion {m n : ℕ} (p : Fin m → PMF (Fin (n + 1)))
    (hp : ∀ i, (p i).support.Finite) (x : ℕ → ℝ) (c : Fin m × Fin n → Bool)
    (w : (tupleLaw m p).support) (i : Fin m) :
    fiberFunctional (tupleLaw m p) (tupleLaw_support_finite m p hp)
      (cutLabel (tupleGridSide m n) c)
      (fun q hq ↦ dispersion q hq (fun a ↦ x (tupleCoordinate m a i).val))
      (cutLabel (tupleGridSide m n) c w) =
    fiberFunctional (p i) (hp i) (cutLabel (indexSide n) (fun j ↦ c (i, j)))
      (fun q hq ↦ dispersion q hq (fun a : Fin (n + 1) ↦ x a.val))
      (cutLabel (indexSide n) (fun j ↦ c (i, j)) (tupleCoordinate m w.val i)) := by
  let μ (j : Fin m) := conditionalAt (p j) (cutLabel (indexSide n) (fun k ↦ c (j, k)))
    (tupleSupportCoordinate m p w j)
  have hμ (j : Fin m) : (μ j).support.Finite := conditionalPMF_support_finite (p j) (hp j) _ _
  let F : (q : PMF (FiniteTuple (Fin (n + 1)) m)) → q.support.Finite → ℝ :=
    fun q hq ↦ dispersion q hq (fun a ↦ x (tupleCoordinate m a i).val)
  let G : (q : PMF (Fin (n + 1))) → q.support.Finite → ℝ :=
    fun q hq ↦ dispersion q hq (fun a ↦ x a.val)
  have h₁ := fiberFunctional_at (tupleLaw m p) (tupleLaw_support_finite m p hp)
    (cutLabel (tupleGridSide m n) c) F w
  have h₂ := finiteFunctional_congr F (conditionalAt_tupleGridCut p c w)
    (conditionalPMF_support_finite (tupleLaw m p) (tupleLaw_support_finite m p hp) _ _)
    (tupleLaw_support_finite m μ hμ)
  have h₃ := dispersion_tupleCoordinate (fun a : Fin (n + 1) ↦ x a.val) m μ hμ i
  have h₄ := fiberFunctional_at (p i) (hp i)
    (cutLabel (indexSide n) (fun j ↦ c (i, j))) G (tupleSupportCoordinate m p w i)
  exact h₁.trans (h₂.trans (h₃.trans h₄.symm))

theorem meanFiberFunctional_tupleGrid_dispersion {m n : ℕ} (p : Fin m → PMF (Fin (n + 1)))
    (hp : ∀ i, (p i).support.Finite) (x : ℕ → ℝ) (c : Fin m × Fin n → Bool) (i : Fin m) :
    meanFiberFunctional (tupleLaw m p) (tupleLaw_support_finite m p hp)
      (cutLabel (tupleGridSide m n) c)
      (fun q hq ↦ dispersion q hq (fun a ↦ x (tupleCoordinate m a i).val)) =
      cellDispersion (p i) (hp i) x (fun j ↦ c (i, j)) := by
  rw [cellDispersion_eq_meanFiberFunctional]
  let F (a : Fin (n + 1)) := fiberFunctional (p i) (hp i)
    (cutLabel (indexSide n) (fun j ↦ c (i, j)))
    (fun q hq ↦ dispersion q hq (fun b ↦ x b.val))
    (cutLabel (indexSide n) (fun j ↦ c (i, j)) a)
  change expectation (tupleLaw m p) (tupleLaw_support_finite m p hp) _ = expectation (p i) (hp i) F
  have he := expectation_map (tupleLaw m p) (tupleLaw_support_finite m p hp)
    (fun w ↦ tupleCoordinate m w i) F
  have hm : expectation ((tupleLaw m p).map (fun w ↦ tupleCoordinate m w i))
      (by simpa using (tupleLaw_support_finite m p hp).image (fun w ↦ tupleCoordinate m w i)) F =
      expectation (p i) (hp i) F := by
    congr 1
    exact tupleLaw_coordinate m p i
  apply Eq.trans _ (he.symm.trans hm)
  unfold expectation
  apply Finset.sum_congr rfl
  intro w hw
  congr 1
  exact fiberFunctional_tupleGrid_dispersion p hp x c ⟨w, by simpa using hw⟩ i

end ExactOverlaps.Poisson
