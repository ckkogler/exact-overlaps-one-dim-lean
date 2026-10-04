module

public import ExactOverlaps.Probability.PairSurvivalIntegral
public import ExactOverlaps.Probability.VarianceRefinement
public import ExactOverlaps.Probability.PoissonContinuity
public import ExactOverlaps.Probability.FinitePositiveIntegration

/-!
# Dispersion inside finite Poisson cells

The unconditional integrated dispersion bound applies to every actual
conditional law in a cut cell. Averaging and independent refinement bound
the mean cell dispersion at time `t` by the future variance curve.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical

namespace ExactOverlaps.Poisson

/-- Mean dispersion inside the observed cells of one finite cut state. -/
noncomputable def cellDispersion {n : ℕ} (p : PMF (Fin (n + 1)))
    (hp : p.support.Finite) (x : ℕ → ℝ) (c : Fin n → Bool) : ℝ :=
  letI : Fintype (p.map (cutLabel (indexSide n) c)).support :=
    (show (p.map (cutLabel (indexSide n) c)).support.Finite from
      by simpa using hp.image (cutLabel (indexSide n) c)).fintype
  ∑ b : (p.map (cutLabel (indexSide n) c)).support,
    ((p.map (cutLabel (indexSide n) c)) b).toReal *
      FiniteLaw.dispersion (Entropy.conditionalPMF p (cutLabel (indexSide n) c) b)
        (Entropy.conditionalPMF_support_finite p hp (cutLabel (indexSide n) c) b)
        (fun a ↦ x a.val)

/-- Mean conditional dispersion after averaging over the actual cut states. -/
noncomputable def cutDispersion {n : ℕ} (p : PMF (Fin (n + 1)))
    (hp : p.support.Finite) (x : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ c : Fin n → Bool, cutWeight (orderedGapLength x n) t c * cellDispersion p hp x c

lemma cellDispersion_nonneg {n : ℕ} (p : PMF (Fin (n + 1)))
    (hp : p.support.Finite) (x : ℕ → ℝ) (c : Fin n → Bool) :
    0 ≤ cellDispersion p hp x c := by
  unfold cellDispersion
  exact Finset.sum_nonneg (fun b _ ↦ mul_nonneg ENNReal.toReal_nonneg
    (FiniteLaw.dispersion_nonneg _ _ _))

lemma continuous_conditionalCutVariance {n : ℕ} (p : PMF (Fin (n + 1)))
    (hp : p.support.Finite) (x : ℕ → ℝ) (c : Fin n → Bool) :
    Continuous (conditionalCutVariance p hp x c) := by
  unfold conditionalCutVariance
  apply continuous_finsetSum
  intro b _
  exact (continuous_cutVariance _ _ x).const_mul _

lemma conditionalCutVariance_nonneg {n : ℕ} (p : PMF (Fin (n + 1)))
    (hp : p.support.Finite) (x : ℕ → ℝ) (hx : MonotoneOn x (Icc 0 n))
    (c : Fin n → Bool) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ conditionalCutVariance p hp x c u := by
  unfold conditionalCutVariance
  exact Finset.sum_nonneg (fun b _ ↦ mul_nonneg ENNReal.toReal_nonneg
    (cutVariance_nonneg _ _ x hx hu))

lemma cellDispersion_le_futureVariance {n : ℕ} (p : PMF (Fin (n + 1)))
    (hp : p.support.Finite) (x : ℕ → ℝ) (hx : MonotoneOn x (Icc 0 n))
    (c : Fin n → Bool) :
    ENNReal.ofReal (cellDispersion p hp x c) ≤
      2 * ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (conditionalCutVariance p hp x c u) := by
  let : Fintype (p.map (cutLabel (indexSide n) c)).support :=
    (show (p.map (cutLabel (indexSide n) c)).support.Finite from
      by simpa using hp.image (cutLabel (indexSide n) c)).fintype
  unfold cellDispersion conditionalCutVariance
  apply FiniteProbability.ofReal_sum_mul_le_lintegral
  · intro b
    exact ENNReal.toReal_nonneg
  · intro b
    exact FiniteLaw.dispersion_nonneg _ _ _
  · intro b
    exact (continuous_cutVariance _ _ x).measurable
  · intro b
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact cutVariance_nonneg _ _ x hx hu.le
  · intro b
    exact dispersion_le_two_lintegral_cutVariance _ _ x hx

/-- Refinement turns the cellwise dispersion bound into a tail of the variance curve. -/
theorem cutDispersion_le_futureVariance {n : ℕ} (p : PMF (Fin (n + 1)))
    (hp : p.support.Finite) (x : ℕ → ℝ) (hx : MonotoneOn x (Icc 0 n))
    (t : ℝ) (ht : 0 ≤ t) :
    ENNReal.ofReal (cutDispersion p hp x t) ≤
      2 * ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (cutVariance p hp x (t + u)) := by
  have h := FiniteProbability.ofReal_sum_mul_le_lintegral (volume.restrict (Ioi (0 : ℝ)))
    (cutWeight (orderedGapLength x n) t) (cellDispersion p hp x)
    (fun c ↦ cutWeight_nonneg _ (orderedGapLength_nonneg x n hx) ht c)
    (cellDispersion_nonneg p hp x) (conditionalCutVariance p hp x)
    (fun c ↦ (continuous_conditionalCutVariance p hp x c).measurable)
    (fun c ↦ by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact conditionalCutVariance_nonneg p hp x hx c hu.le)
    2 (cellDispersion_le_futureVariance p hp x hx)
  change ENNReal.ofReal (cutDispersion p hp x t) ≤ _ at h
  refine h.trans_eq ?_
  congr 1
  apply lintegral_congr
  intro u
  rw [average_conditionalCutVariance]

end ExactOverlaps.Poisson
