module

public import ExactOverlaps.Probability.PoissonVariance
import Mathlib.Tactic.FunProp

/-!
# Continuity of finite cut probabilities and variance averages

Every finite cut-state weight is a product of exponential factors. Finite
averages of conditional moments are therefore continuous in the intensity.
-/

@[expose] public section

open scoped BigOperators Classical

namespace ExactOverlaps.Poisson

lemma continuous_cutWeight {ι : Type*} [Fintype ι] (d : ι → ℝ) (c : ι → Bool) :
    Continuous (fun t ↦ cutWeight d t c) := by
  unfold cutWeight
  apply continuous_finsetProd
  intro i _
  by_cases hc : c i = true
  · simp only [hc, ite_true]
    fun_prop
  · simp only [hc, Bool.false_eq_true, ite_false]
    fun_prop

lemma continuous_cutVariance {n : ℕ} (p : PMF (Fin (n + 1)))
    (hp : p.support.Finite) (x : ℕ → ℝ) : Continuous (cutVariance p hp x) := by
  unfold cutVariance
  apply continuous_finsetSum
  intro c _
  exact (continuous_cutWeight (orderedGapLength x n) c).mul_const _

end ExactOverlaps.Poisson
