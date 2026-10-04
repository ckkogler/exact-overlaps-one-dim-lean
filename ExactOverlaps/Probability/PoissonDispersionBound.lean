module

public import ExactOverlaps.Probability.ConditionalDispersion
public import ExactOverlaps.Probability.PositiveTriangleIntegral

/-!
# Integrated dispersion bound for finite ordered supports

This proves the inequality part of the Poisson dispersion comparison. The
separate identity relating the variance curve to interval variance energy
is not assumed here.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical

namespace ExactOverlaps.Poisson

lemma cutDispersion_nonneg {n : ℕ} (p : PMF (Fin (n + 1)))
    (hp : p.support.Finite) (x : ℕ → ℝ) (hx : MonotoneOn x (Icc 0 n))
    {t : ℝ} (ht : 0 ≤ t) : 0 ≤ cutDispersion p hp x t := by
  exact Finset.sum_nonneg (fun c _ ↦ mul_nonneg
    (cutWeight_nonneg _ (orderedGapLength_nonneg x n hx) ht c)
    (cellDispersion_nonneg p hp x c))

lemma continuous_cutDispersion {n : ℕ} (p : PMF (Fin (n + 1)))
    (hp : p.support.Finite) (x : ℕ → ℝ) : Continuous (cutDispersion p hp x) := by
  unfold cutDispersion
  apply continuous_finsetSum
  intro c _
  exact (continuous_cutWeight (orderedGapLength x n) c).mul_const _

/-- Integrating dispersion over refinement time is bounded by twice the variance first moment. -/
theorem lintegral_cutDispersion_le {n : ℕ} (p : PMF (Fin (n + 1)))
    (hp : p.support.Finite) (x : ℕ → ℝ) (hx : MonotoneOn x (Icc 0 n)) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (cutDispersion p hp x t)) ≤
      2 * ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t * cutVariance p hp x t) := by
  calc
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (cutDispersion p hp x t)) ≤
        ∫⁻ t in Ioi (0 : ℝ),
          2 * ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (cutVariance p hp x (t + u)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact cutDispersion_le_futureVariance p hp x hx t ht.le
    _ = 2 * ∫⁻ t in Ioi (0 : ℝ),
        ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (cutVariance p hp x (t + u)) :=
      lintegral_const_mul' _ _ (by norm_num)
    _ = 2 * ∫⁻ t in Ioi (0 : ℝ),
        ENNReal.ofReal t * ENNReal.ofReal (cutVariance p hp x t) := by
      rw [lintegral_positive_triangle _ (continuous_cutVariance p hp x).measurable.ennreal_ofReal]
    _ = _ := by
      congr 1
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [ENNReal.ofReal_mul ht.le]

end ExactOverlaps.Poisson
