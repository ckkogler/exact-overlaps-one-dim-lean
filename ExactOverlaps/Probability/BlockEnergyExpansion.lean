module

public import ExactOverlaps.Probability.BlockEnergyKernels

/-!
# Pointwise finite block expansions of the two energy integrands

Empty and singleton index blocks have zero quadratic error. Removing them
makes the positive-diameter kernel conversion applicable to every summand.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical

namespace ExactOverlaps.Poisson

lemma blockVarianceMass_eq_zero_of_not_lt {n : ℕ} (p : PMF (Fin (n + 1)))
    (hp : p.support.Finite) (x : Fin (n + 1) → ℝ) (a b : Fin (n + 1))
    (hab : ¬ a < b) : blockVarianceMass p hp x a b = 0 := by
  rcases lt_or_eq_of_le (le_of_not_gt hab) with hba | he
  · have hw : (fun z ↦ if z ∈ Finset.Icc a b then (p z).toReal else 0) =
        (fun _ ↦ (0 : ℝ)) := by
      funext z
      have hz : z ∉ Finset.Icc a b := by
        intro h
        exact (not_le_of_gt hba) ((Finset.mem_Icc.mp h).1.trans (Finset.mem_Icc.mp h).2)
      simp [hz]
    unfold blockVarianceMass
    rw [hw]
    simp [FiniteLaw.minimumQuadraticError, FiniteLaw.quadraticError]
  · subst b
    exact blockVarianceMass_singleton p hp x a

lemma time_cutVariance_eq_blocks {n : ℕ} (p : PMF (Fin (n + 1)))
    (hp : p.support.Finite) (x : ℕ → ℝ) (t : ℝ) :
    t * cutVariance p hp x t = ∑ a : Fin (n + 1), ∑ b : Fin (n + 1),
      blockVarianceMass p hp (fun z ↦ x z.val) a b * blockTimeKernel x a b t := by
  rw [cutVariance_eq_blocks]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases hab : a < b
  · simp only [blockTimeKernel, hab, ite_true]
    ring
  · rw [blockVarianceMass_eq_zero_of_not_lt p hp _ a b hab]
    simp

lemma varianceEnergy_integrand_eq_blocks {n : ℕ} (p : PMF (Fin (n + 1)))
    (hp : p.support.Finite) (x : Fin (n + 1) → ℝ) (hx : Monotone x)
    {r : ℝ} (hr : 0 < r) :
    VarianceEnergy.normalizedLocalVariance (p.map x).toMeasure r * ENNReal.ofReal (1 / r) =
      4 * ∑ a : Fin (n + 1), ∑ b : Fin (n + 1),
        ENNReal.ofReal (blockVarianceMass p hp x a b) * blockEnergyKernel x a b r := by
  rw [VarianceEnergy.normalizedLocalVariance, lintegral_localVarianceMass_eq_blocks p hp x hx]
  have hfactor : ENNReal.ofReal (4 / r ^ 3) * ENNReal.ofReal (1 / r) =
      4 * ENNReal.ofReal (1 / r ^ 4) := by
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4 / r ^ 3)]
    have he : 4 / r ^ 3 * (1 / r) = 4 * (1 / r ^ 4) := by
      field_simp
    rw [he, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases hab : a < b
  · simp only [hab.le, ite_true, blockEnergyKernel, hab]
    calc
      ENNReal.ofReal (4 / r ^ 3) *
          (ENNReal.ofReal (blockVarianceMass p hp x a b) * volume (windowOrigins x r a b)) *
          ENNReal.ofReal (1 / r) =
        (ENNReal.ofReal (4 / r ^ 3) * ENNReal.ofReal (1 / r)) *
          (ENNReal.ofReal (blockVarianceMass p hp x a b) * volume (windowOrigins x r a b)) := by ring
      _ = _ := by rw [hfactor]; ring
  · rw [blockVarianceMass_eq_zero_of_not_lt p hp x a b hab]
    simp

end ExactOverlaps.Poisson
