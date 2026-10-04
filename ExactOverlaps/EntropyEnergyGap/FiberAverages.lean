module

public import ExactOverlaps.Probability.FiberAverages
public import ExactOverlaps.Entropy.ConditionalConcavity

/-!
# Constant terms in conditional-functional averages

Positive observation fibers have total probability one. Adding the same
constant inside every actual conditional law therefore adds it once to
the average, including when some ambient observation labels have zero mass.
-/

@[expose] public section

open scoped BigOperators Classical
open ExactOverlaps.Entropy ExactOverlaps.FiniteProbability

namespace ExactOverlaps.EntropyEnergyGap

lemma meanFiberFunctional_add_const {α β : Type*} (p : PMF α) (hp : p.support.Finite)
    (f : α → β) (F : (q : PMF α) → q.support.Finite → ℝ) (c : ℝ) :
    meanFiberFunctional p hp f (fun q hq ↦ F q hq + c) = meanFiberFunctional p hp f F + c := by
  let : Fintype (p.map f).support :=
    (show (p.map f).support.Finite from by simpa using hp.image f).fintype
  have hs : (∑ b : (p.map f).support, ((p.map f) b).toReal) = 1 :=
    sum_pmf_toReal (supportLaw (p.map f))
  rw [meanFiberFunctional_eq_sum, meanFiberFunctional_eq_sum]
  simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hs, one_mul]

end ExactOverlaps.EntropyEnergyGap
