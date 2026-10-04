module

public import ExactOverlaps.Entropy.FiniteTupleExt
public import ExactOverlaps.Probability.FiniteProductConditioning
public import ExactOverlaps.Probability.OrderedGapCuts

/-!
# Rectangular cells of a finite family of grid cuts

Flattening all coordinate cut labels does not change any observation fiber.
Conditioning the actual product input law on that flattened label therefore
gives exactly the product of the genuine coordinate cell laws.
-/

@[expose] public section

open scoped Classical
open ExactOverlaps.Entropy ExactOverlaps.FiniteProbability

namespace ExactOverlaps.Poisson

def tupleGridSide (m n : ℕ) (i : Fin m × Fin n) (w : FiniteTuple (Fin (n + 1)) m) : Bool :=
  indexSide n i.2 (tupleCoordinate m w i.1)

def rectangularGridLabel (m n : ℕ) (c : Fin m × Fin n → Bool) :
    FiniteTuple (Fin (n + 1)) m → FiniteTuple (Fin n → Bool) m :=
  tupleMap m (fun i ↦ cutLabel (indexSide n) (fun j ↦ c (i, j)))

lemma tupleGridLabel_eq_iff_rectangular {m n : ℕ} (c : Fin m × Fin n → Bool)
    (a b : FiniteTuple (Fin (n + 1)) m) :
    cutLabel (tupleGridSide m n) c a = cutLabel (tupleGridSide m n) c b ↔
      rectangularGridLabel m n c a = rectangularGridLabel m n c b := by
  rw [tuple_eq_iff_coordinate_eq]
  constructor
  · intro h i
    funext j
    have hij := congrArg (fun z ↦ z (i, j)) h
    simpa only [rectangularGridLabel, tupleCoordinate_tupleMap, cutLabel, tupleGridSide] using hij
  · intro h
    funext ij
    have hij := congrArg (fun z ↦ z ij.2) (h ij.1)
    simpa only [rectangularGridLabel, tupleCoordinate_tupleMap, cutLabel, tupleGridSide] using hij

theorem conditionalAt_tupleGridCut {m n : ℕ} (p : Fin m → PMF (Fin (n + 1)))
    (c : Fin m × Fin n → Bool) (w : (tupleLaw m p).support) :
    conditionalAt (tupleLaw m p) (cutLabel (tupleGridSide m n) c) w =
      tupleLaw m (fun i ↦ conditionalAt (p i) (cutLabel (indexSide n) (fun j ↦ c (i, j)))
        (tupleSupportCoordinate m p w i)) := by
  calc
    _ = conditionalAt (tupleLaw m p) (rectangularGridLabel m n c) w :=
      conditionalAt_eq_of_fiber_eq (tupleLaw m p) _ _ w
        (fun a ↦ tupleGridLabel_eq_iff_rectangular c a w.val)
    _ = _ := conditionalAt_tupleLaw m p
      (fun i ↦ cutLabel (indexSide n) (fun j ↦ c (i, j))) w

end ExactOverlaps.Poisson
