module

public import ExactOverlaps.Entropy.FiniteProductLaw

/-!
# Entropy of actual independent finite tuples

The recursively constructed product PMF has entropy equal to the sum of its
marginal entropies. This identifies the joint-entropy term in the terminal
information loss without assuming entropy additivity as a premise.
-/

@[expose] public section

open scoped BigOperators Classical

namespace ExactOverlaps.Entropy

lemma finiteEntropy_pure {α : Type*} (a : α) (h : (PMF.pure a).support.Finite) :
    finiteEntropy (PMF.pure a) h = 0 := by
  simp [finiteEntropy, PMF.support_pure]

theorem finiteEntropy_tupleLaw {α : Type*} (n : ℕ) (p : Fin n → PMF α)
    (hp : ∀ i, (p i).support.Finite) :
    finiteEntropy (tupleLaw n p) (tupleLaw_support_finite n p hp) =
      ∑ i, finiteEntropy (p i) (hp i) := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact finiteEntropy_pure PUnit.unit _
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    change finiteEntropy (independentPair (p 0) (tupleLaw n (fun i ↦ p i.succ))) _ = _
    rw [finiteEntropy_independentPair (p 0) (tupleLaw n (fun i ↦ p i.succ)) (hp 0)
      (tupleLaw_support_finite n (fun i ↦ p i.succ) (fun i ↦ hp i.succ)),
      ih (fun i ↦ p i.succ) (fun i ↦ hp i.succ)]

end ExactOverlaps.Entropy
