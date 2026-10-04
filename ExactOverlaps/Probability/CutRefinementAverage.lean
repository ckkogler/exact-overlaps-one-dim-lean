module

public import ExactOverlaps.Probability.PoissonRefinement
import Mathlib.Tactic.Ring

/-!
# Averaging functions of independently refined cut states

The cut-state superposition law holds for every real-valued function of the
resulting state. This finite sum form is the interface for entropy, variance
and dispersion functionals of the observed partition.
-/

@[expose] public section

open scoped BigOperators Classical

namespace ExactOverlaps.Poisson

lemma sum_cutWeight_union_apply {ι : Type*} [Fintype ι] (d : ι → ℝ) (t u : ℝ)
    (F : (ι → Bool) → ℝ) :
    (∑ c : ι → Bool, cutWeight d t c *
      ∑ c' : ι → Bool, cutWeight d u c' * F (unionCuts c c')) =
      ∑ z : ι → Bool, cutWeight d (t + u) z * F z := by
  have hz (z : ι → Bool) : cutWeight d (t + u) z * F z =
      ∑ c : ι → Bool, ∑ c' : ι → Bool,
        if unionCuts c c' = z then cutWeight d t c * cutWeight d u c' * F z else 0 := by
    rw [← sum_cutWeight_union d t u z]
    simp_rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro c' _
    split_ifs <;> simp
  simp_rw [hz, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c' _
  rw [Finset.sum_eq_single (unionCuts c c')]
  · simp only [ite_true]
    ring
  · intro z _ hz
    simp [Ne.symm hz]
  · simp

end ExactOverlaps.Poisson
