module

public import ExactOverlaps.Probability.BlockEnergyExpansion
public import ExactOverlaps.Probability.PoissonDispersionBound

/-!
# Poisson dispersion and the genuine variance energy on ordered finite laws

Both integrals are expanded using the same quadratic-error coefficients.
The block conversion has factor six, while variance energy has normalization
four. Together with the refinement inequality this gives the constant three.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical

namespace ExactOverlaps.Poisson

lemma energy_eq_four_sum_blocks {n : ℕ} (p : PMF (Fin (n + 1)))
    (hp : p.support.Finite) (x : Fin (n + 1) → ℝ) (hx : Monotone x) :
    VarianceEnergy.energy (p.map x).toMeasure =
      4 * ∑ a : Fin (n + 1), ∑ b : Fin (n + 1),
        ENNReal.ofReal (blockVarianceMass p hp x a b) *
          ∫⁻ r in Ioi (0 : ℝ), blockEnergyKernel x a b r := by
  unfold VarianceEnergy.energy
  have he : (∫⁻ r in Ioi (0 : ℝ),
      VarianceEnergy.normalizedLocalVariance (p.map x).toMeasure r * ENNReal.ofReal (1 / r)) =
      ∫⁻ r in Ioi (0 : ℝ), 4 * ∑ a : Fin (n + 1), ∑ b : Fin (n + 1),
        ENNReal.ofReal (blockVarianceMass p hp x a b) * blockEnergyKernel x a b r := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact varianceEnergy_integrand_eq_blocks p hp x hx hr
  rw [he, lintegral_const_mul' _ _ (by norm_num : (4 : ℝ≥0∞) ≠ ∞)]
  congr 1
  rw [lintegral_finsetSum _ (fun a _ ↦ Finset.measurable_sum _ (fun b _ ↦
    (measurable_blockEnergyKernel x hx a b).const_mul _))]
  apply Finset.sum_congr rfl
  intro a _
  rw [lintegral_finsetSum _ (fun b _ ↦ (measurable_blockEnergyKernel x hx a b).const_mul _)]
  apply Finset.sum_congr rfl
  intro b _
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

lemma lintegral_time_cutVariance_eq_six_sum_blocks {n : ℕ} (p : PMF (Fin (n + 1)))
    (hp : p.support.Finite) (x : ℕ → ℝ)
    (hx : StrictMono (fun z : Fin (n + 1) ↦ x z.val)) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t * cutVariance p hp x t)) =
      6 * ∑ a : Fin (n + 1), ∑ b : Fin (n + 1),
        ENNReal.ofReal (blockVarianceMass p hp (fun z ↦ x z.val) a b) *
          ∫⁻ r in Ioi (0 : ℝ), blockEnergyKernel (fun z ↦ x z.val) a b r := by
  have hsum := FiniteProbability.lintegral_ofReal_sum_mul (volume.restrict (Ioi (0 : ℝ)))
    (fun z : Fin (n + 1) × Fin (n + 1) ↦ blockVarianceMass p hp (fun z ↦ x z.val) z.1 z.2)
    (fun z ↦ blockVarianceMass_nonneg p hp _ z.1 z.2)
    (fun z t ↦ blockTimeKernel x z.1 z.2 t)
    (fun z ↦ (continuous_blockTimeKernel x z.1 z.2).measurable)
    (fun z ↦ by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact blockTimeKernel_nonneg x hx.monotone z.1 z.2 ht.le)
  simp only [Fintype.sum_prod_type] at hsum
  simp_rw [time_cutVariance_eq_blocks]
  rw [hsum]
  simp_rw [lintegral_blockTimeKernel x hx]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem two_lintegral_time_cutVariance_eq_three_energy {n : ℕ} (p : PMF (Fin (n + 1)))
    (hp : p.support.Finite) (x : ℕ → ℝ)
    (hx : StrictMono (fun z : Fin (n + 1) ↦ x z.val)) :
    2 * (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t * cutVariance p hp x t)) =
      3 * VarianceEnergy.energy (p.map (fun z ↦ x z.val)).toMeasure := by
  rw [lintegral_time_cutVariance_eq_six_sum_blocks p hp x hx,
    energy_eq_four_sum_blocks p hp _ hx.monotone]
  ring

/-- The complete dispersion/energy comparison for a genuine ordered finite law. -/
theorem lintegral_cutDispersion_le_three_energy {n : ℕ} (p : PMF (Fin (n + 1)))
    (hp : p.support.Finite) (x : ℕ → ℝ)
    (hx : StrictMono (fun z : Fin (n + 1) ↦ x z.val)) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (cutDispersion p hp x t)) ≤
      3 * VarianceEnergy.energy (p.map (fun z ↦ x z.val)).toMeasure := by
  have hmono : MonotoneOn x (Icc 0 n) := by
    intro a ha b hb hab
    exact hx.monotone (show (⟨a, Nat.lt_succ_iff.mpr ha.2⟩ : Fin (n + 1)) ≤
      ⟨b, Nat.lt_succ_iff.mpr hb.2⟩ from hab)
  exact (lintegral_cutDispersion_le p hp x hmono).trans_eq
    (two_lintegral_time_cutVariance_eq_three_energy p hp x hx)

end ExactOverlaps.Poisson
