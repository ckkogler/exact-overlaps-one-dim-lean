module

public import ExactOverlaps.Probability.PoissonVariance
public import ExactOverlaps.Probability.FiniteIntegration
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Integrated pair survival and dispersion

The exponential independent-copy kernel integrates exactly to the mean
absolute distance. Integrating its pointwise variance bound uses nonnegative
integrals, so no finiteness of the variance curve is assumed in advance.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical

namespace ExactOverlaps.Poisson

lemma integrableOn_sq_mul_exp_abs (d : ℝ) :
    IntegrableOn (fun t : ℝ ↦ d ^ 2 * Real.exp (-(|d| * t))) (Ioi 0) := by
  by_cases hd : d = 0
  · simp [hd]
  · have h := (integrableOn_pow_mul_exp (abs_pos.mpr hd) 0).const_mul (d ^ 2)
    apply h.congr
    exact Filter.Eventually.of_forall (fun t ↦ by simp)

lemma integral_sq_mul_exp_abs (d : ℝ) :
    (∫ t : ℝ in Ioi 0, d ^ 2 * Real.exp (-(|d| * t))) = |d| := by
  by_cases hd : d = 0
  · simp [hd]
  · have h := integral_pow_mul_exp (abs_pos.mpr hd) 0
    simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one] at h
    rw [integral_const_mul, h, ← sq_abs]
    field_simp

lemma pairSurvival_eq_expectation {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (x : α → ℝ) (t : ℝ) :
    pairSurvival p hp x t = FiniteProbability.expectation p hp (fun a ↦
      FiniteProbability.expectation p hp (fun b ↦
        (x a - x b) ^ 2 * Real.exp (-(|x a - x b| * t)))) := by
  unfold pairSurvival FiniteProbability.expectation
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

lemma integrableOn_pairSurvival {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (x : α → ℝ) : IntegrableOn (pairSurvival p hp x) (Ioi 0) := by
  change IntegrableOn (fun t ↦ pairSurvival p hp x t) (Ioi 0)
  simp_rw [pairSurvival_eq_expectation]
  apply FiniteProbability.integrable_expectation
  intro a _
  apply FiniteProbability.integrable_expectation
  intro b _
  exact integrableOn_sq_mul_exp_abs (x a - x b)

lemma integral_pairSurvival {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (x : α → ℝ) :
    (∫ t : ℝ in Ioi 0, pairSurvival p hp x t) = FiniteLaw.dispersion p hp x := by
  have hi (a : α) : IntegrableOn (fun t : ℝ ↦ FiniteProbability.expectation p hp
      (fun b ↦ (x a - x b) ^ 2 * Real.exp (-(|x a - x b| * t)))) (Ioi 0) := by
    apply FiniteProbability.integrable_expectation
    intro b _
    exact integrableOn_sq_mul_exp_abs (x a - x b)
  have he (a : α) : (∫ t : ℝ in Ioi 0, FiniteProbability.expectation p hp
      (fun b ↦ (x a - x b) ^ 2 * Real.exp (-(|x a - x b| * t)))) =
      FiniteProbability.expectation p hp (fun b ↦ |x a - x b|) := by
    rw [FiniteProbability.integral_expectation p hp _
      (fun b _ ↦ integrableOn_sq_mul_exp_abs (x a - x b))]
    simp_rw [integral_sq_mul_exp_abs]
  simp_rw [pairSurvival_eq_expectation]
  rw [FiniteProbability.integral_expectation p hp _ (fun a _ ↦ hi a)]
  simp_rw [he]
  rfl

lemma pairSurvival_nonneg {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (x : α → ℝ) (t : ℝ) : 0 ≤ pairSurvival p hp x t := by
  unfold pairSurvival
  exact Finset.sum_nonneg (fun a _ ↦ Finset.sum_nonneg (fun b _ ↦
    mul_nonneg (mul_nonneg (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      (sq_nonneg _)) (Real.exp_pos _).le))

/-- The first integrated dispersion bound, before any variance-curve finiteness claim. -/
theorem dispersion_le_two_lintegral_cutVariance {n : ℕ} (p : PMF (Fin (n + 1)))
    (hp : p.support.Finite) (x : ℕ → ℝ) (hx : MonotoneOn x (Icc 0 n)) :
    ENNReal.ofReal (FiniteLaw.dispersion p hp (fun a ↦ x a.val)) ≤
      2 * ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (cutVariance p hp x t) := by
  rw [← integral_pairSurvival p hp (fun a ↦ x a.val),
    ofReal_integral_eq_lintegral_ofReal (integrableOn_pairSurvival p hp (fun a ↦ x a.val))
      (Filter.Eventually.of_forall (fun t ↦ pairSurvival_nonneg p hp _ t))]
  calc
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (pairSurvival p hp (fun a ↦ x a.val) t)) ≤
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (2 * cutVariance p hp x t) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact ENNReal.ofReal_le_ofReal (pairSurvival_le_two_cutVariance p hp x hx t ht.le)
    _ = _ := by
      simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
      exact lintegral_const_mul' _ _ (by norm_num)

end ExactOverlaps.Poisson
