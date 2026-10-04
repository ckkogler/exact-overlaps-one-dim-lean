module

public import ExactOverlaps.Entropy.FiniteProductMaps

/-!
# Exact sum laws under coordinatewise recoding

Pushing each marginal through one real statistic and then adding gives
exactly the push-forward of the original product law by the statistic sum.
-/

@[expose] public section

namespace ExactOverlaps.Entropy

lemma tupleSum_tupleMap {α β : Type*} (n : ℕ) (f : α → β) (g : β → ℝ)
    (w : FiniteTuple α n) :
    tupleSum g n (tupleMap n (fun _ ↦ f) w) = tupleSum (g ∘ f) n w := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change g (f w.1) + tupleSum g n (tupleMap n (fun _ ↦ f) w.2) =
      g (f w.1) + tupleSum (g ∘ f) n w.2
    rw [ih]

theorem tupleLaw_sum_map {α β : Type*} (n : ℕ) (p : Fin n → PMF α)
    (f : α → β) (g : β → ℝ) :
    (tupleLaw n (fun i ↦ (p i).map f)).map (tupleSum g n) =
      (tupleLaw n p).map (tupleSum (g ∘ f) n) := by
  rw [← tupleLaw_map n p (fun _ ↦ f), PMF.map_comp]
  congr 1
  funext w
  exact tupleSum_tupleMap n f g w

end ExactOverlaps.Entropy
