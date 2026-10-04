module

public import ExactOverlaps.EntropyEnergyGap.FiberAverages

/-!
# Actual conditional entropy as a fiber-functional average

The ordinary finite Shannon conditional entropy is the average of the
genuine conditional laws. Conditioning also bounds the mean entropy of
any statistic by its unconditional entropy.
-/

@[expose] public section

open scoped BigOperators Classical
open ExactOverlaps.Entropy ExactOverlaps.FiniteProbability

namespace ExactOverlaps.EntropyEnergyGap

lemma meanFiberFunctional_add {α β : Type*} (p : PMF α) (hp : p.support.Finite)
    (f : α → β) (F G : (q : PMF α) → q.support.Finite → ℝ) :
    meanFiberFunctional p hp f (fun q hq ↦ F q hq + G q hq) =
      meanFiberFunctional p hp f F + meanFiberFunctional p hp f G := by
  rw [meanFiberFunctional_eq_sum, meanFiberFunctional_eq_sum, meanFiberFunctional_eq_sum]
  simp_rw [mul_add, Finset.sum_add_distrib]

lemma mean_entropy_eq_conditional {α β : Type*} (p : PMF α) (hp : p.support.Finite)
    (f : α → β) :
    meanFiberFunctional p hp f (fun q hq ↦ finiteEntropy q hq) = conditionalEntropy p hp f := by
  rw [meanFiberFunctional_eq_sum, conditionalEntropy_eq_average]
  rfl

lemma mean_map_entropy_le {α β γ : Type*} (p : PMF α) (hp : p.support.Finite)
    (f : α → β) (g : α → γ) :
    meanFiberFunctional p hp f
      (fun q hq ↦ finiteEntropy (q.map g) (by simpa using hq.image g)) ≤
      finiteEntropy (p.map g) (by simpa using hp.image g) := by
  rw [meanFiberFunctional_eq_sum]
  exact average_conditional_map_entropy_le p hp f g

end ExactOverlaps.EntropyEnergyGap
