module

public import ExactOverlaps.Probability.FiniteProductConditioning
public import ExactOverlaps.Probability.FiberAverages

/-!
# Marginal functionals after rectangular product conditioning

Every conditional product has the actual conditional marginal laws.
Averaging a functional of one such marginal over the joint labels
therefore equals its one-coordinate conditional average.
-/

@[expose] public section

open scoped BigOperators Classical
open ExactOverlaps.Entropy ExactOverlaps.FiniteProbability

namespace ExactOverlaps.EntropyEnergyGap

noncomputable def coordinateFunctional {α : Type*} (m : ℕ) (i : Fin m)
    (F : (p : PMF α) → p.support.Finite → ℝ)
    (q : PMF (FiniteTuple α m)) (hq : q.support.Finite) : ℝ :=
  F (q.map (fun w ↦ tupleCoordinate m w i))
    (by simpa using hq.image (fun w ↦ tupleCoordinate m w i))

lemma coordinateFunctional_tupleLaw {α : Type*} (m : ℕ) (p : Fin m → PMF α)
    (hp : ∀ i, (p i).support.Finite) (i : Fin m)
    (F : (q : PMF α) → q.support.Finite → ℝ) :
    coordinateFunctional m i F (tupleLaw m p) (tupleLaw_support_finite m p hp) = F (p i) (hp i) :=
  finiteFunctional_congr F (tupleLaw_coordinate m p i) _ _

lemma fiberFunctional_product_coordinate {α β : Type*} (m : ℕ) (p : Fin m → PMF α)
    (hp : ∀ i, (p i).support.Finite) (f : Fin m → α → β)
    (F : (q : PMF α) → q.support.Finite → ℝ) (w : (tupleLaw m p).support) (i : Fin m) :
    fiberFunctional (tupleLaw m p) (tupleLaw_support_finite m p hp) (tupleMap m f)
      (coordinateFunctional m i F) (tupleMap m f w) =
      fiberFunctional (p i) (hp i) (f i) F (f i (tupleCoordinate m w.val i)) := by
  let μ (j : Fin m) := conditionalAt (p j) (f j) (tupleSupportCoordinate m p w j)
  have hμ (j : Fin m) : (μ j).support.Finite := conditionalPMF_support_finite (p j) (hp j) _ _
  have h₁ := fiberFunctional_at (tupleLaw m p) (tupleLaw_support_finite m p hp)
    (tupleMap m f) (coordinateFunctional m i F) w
  have h₂ := finiteFunctional_congr (coordinateFunctional m i F) (conditionalAt_tupleLaw m p f w)
    (conditionalPMF_support_finite (tupleLaw m p) (tupleLaw_support_finite m p hp) _ _)
    (tupleLaw_support_finite m μ hμ)
  have h₃ := coordinateFunctional_tupleLaw m μ hμ i F
  have h₄ := fiberFunctional_at (p i) (hp i) (f i) F (tupleSupportCoordinate m p w i)
  exact h₁.trans (h₂.trans (h₃.trans h₄.symm))

theorem mean_product_coordinate {α β : Type*} (m : ℕ) (p : Fin m → PMF α)
    (hp : ∀ i, (p i).support.Finite) (f : Fin m → α → β)
    (F : (q : PMF α) → q.support.Finite → ℝ) (i : Fin m) :
    meanFiberFunctional (tupleLaw m p) (tupleLaw_support_finite m p hp) (tupleMap m f)
      (coordinateFunctional m i F) = meanFiberFunctional (p i) (hp i) (f i) F := by
  let G (a : α) := fiberFunctional (p i) (hp i) (f i) F (f i a)
  change expectation (tupleLaw m p) (tupleLaw_support_finite m p hp) _ = expectation (p i) (hp i) G
  have he := expectation_map (tupleLaw m p) (tupleLaw_support_finite m p hp)
    (fun w ↦ tupleCoordinate m w i) G
  have hm : expectation ((tupleLaw m p).map (fun w ↦ tupleCoordinate m w i))
      (by simpa using (tupleLaw_support_finite m p hp).image (fun w ↦ tupleCoordinate m w i)) G =
      expectation (p i) (hp i) G := by
    congr 1
    exact tupleLaw_coordinate m p i
  apply Eq.trans _ (he.symm.trans hm)
  unfold expectation
  apply Finset.sum_congr rfl
  intro w hw
  congr 1
  exact fiberFunctional_product_coordinate m p hp f F ⟨w, by simpa using hw⟩ i

theorem mean_product_coordinate_sum {α β : Type*} (m : ℕ) (p : Fin m → PMF α)
    (hp : ∀ i, (p i).support.Finite) (f : Fin m → α → β)
    (F : (q : PMF α) → q.support.Finite → ℝ) :
    meanFiberFunctional (tupleLaw m p) (tupleLaw_support_finite m p hp) (tupleMap m f)
      (fun q hq ↦ ∑ i, coordinateFunctional m i F q hq) =
      ∑ i, meanFiberFunctional (p i) (hp i) (f i) F := by
  rw [meanFiberFunctional_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact mean_product_coordinate m p hp f F i

end ExactOverlaps.EntropyEnergyGap
