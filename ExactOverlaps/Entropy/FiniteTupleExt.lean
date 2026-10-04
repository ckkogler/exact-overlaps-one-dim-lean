module

public import ExactOverlaps.Entropy.FiniteProductMaps

/-!
# Extensionality of finite independent tuple coordinates

The nested product representation is determined exactly by its indexed
coordinates. This identifies rectangular observation fibers with flattened
families of coordinate labels.
-/

@[expose] public section

namespace ExactOverlaps.Entropy

lemma tuple_eq_iff_coordinate_eq {α : Type*} (n : ℕ) (a b : FiniteTuple α n) :
    a = b ↔ ∀ i, tupleCoordinate n a i = tupleCoordinate n b i := by
  constructor
  · intro h
    subst b
    intro _
    rfl
  · intro h
    induction n with
    | zero => cases a; cases b; rfl
    | succ n ih =>
      exact Prod.ext (h 0) (ih a.2 b.2 (fun i ↦ h i.succ))

end ExactOverlaps.Entropy
