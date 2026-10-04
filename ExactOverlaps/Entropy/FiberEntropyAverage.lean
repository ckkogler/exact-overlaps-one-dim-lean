module

public import ExactOverlaps.Entropy.ConditionalEntropyTower
public import ExactOverlaps.Probability.FiberAverages

/-!
# Functional form of the genuine conditional entropy tower

This interface writes the entropy tower using the shared conditional-law
functional average, so finite linear combinations can be averaged without
changing the actual normalized fiber laws.
-/

@[expose] public section

open ExactOverlaps.FiniteProbability

namespace ExactOverlaps.Entropy

lemma meanFiberFunctional_conditionalEntropy {α β γ δ : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (g : α → γ) (h : α → δ) :
    meanFiberFunctional p hp f (fun q hq ↦ averageStatisticConditionalEntropy q hq g h) =
      averageStatisticConditionalEntropy p hp (fun a ↦ (f a, g a)) h := by
  rw [meanFiberFunctional_eq_sum]
  exact averageStatisticConditionalEntropy_tower p hp f g h

end ExactOverlaps.Entropy
