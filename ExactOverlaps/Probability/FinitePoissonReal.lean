module

public import ExactOverlaps.Probability.FinitePoissonEnergy
public import ExactOverlaps.VarianceEnergy.FiniteEnergy

/-!
# Finite real-integral form of the Poisson dispersion comparison

The energy of a finite real law is finite. The nonnegative integral bounds
therefore imply actual integrability of both Poisson quantities before the
comparison is converted to ordinary real integrals.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ExactOverlaps.Poisson

lemma finiteLaw_energy_ne_top (p : PMF ℝ) (hp : p.support.Finite) :
    VarianceEnergy.energy p.toMeasure ≠ ∞ := by
  apply VarianceEnergy.energy_ne_top_of_finite_support p.toMeasure hp.toFinset
  rw [ae_iff]
  change p.toMeasure ((hp.toFinset : Set ℝ)ᶜ) = 0
  apply (p.toMeasure_apply_eq_zero_iff hp.toFinset.measurableSet.compl).mpr
  apply Set.disjoint_left.mpr
  intro a ha hb
  exact hb (by simpa using ha)

lemma continuous_finitePoissonDispersion (p : PMF ℝ) (hp : p.support.Finite) :
    Continuous (finitePoissonDispersion p hp) := by
  exact continuous_cutDispersion _ _ _

lemma continuous_finitePoissonVariance (p : PMF ℝ) (hp : p.support.Finite) :
    Continuous (finitePoissonVariance p hp) := by
  exact continuous_cutVariance _ _ _

lemma finitePoissonDispersion_nonneg (p : PMF ℝ) (hp : p.support.Finite)
    {t : ℝ} (ht : 0 ≤ t) : 0 ≤ finitePoissonDispersion p hp t := by
  exact cutDispersion_nonneg _ _ _
    (orderedPresentation_monotoneOn (orderedFinitePresentation p hp)) ht

lemma finitePoissonVariance_nonneg (p : PMF ℝ) (hp : p.support.Finite)
    {t : ℝ} (ht : 0 ≤ t) : 0 ≤ finitePoissonVariance p hp t := by
  exact cutVariance_nonneg _ _ _
    (orderedPresentation_monotoneOn (orderedFinitePresentation p hp)) ht

lemma finitePoissonDispersion_ae_nonneg (p : PMF ℝ) (hp : p.support.Finite) :
    ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), 0 ≤ finitePoissonDispersion p hp t := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact finitePoissonDispersion_nonneg p hp ht.le

lemma time_finitePoissonVariance_ae_nonneg (p : PMF ℝ) (hp : p.support.Finite) :
    ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), 0 ≤ t * finitePoissonVariance p hp t := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact mul_nonneg ht.le (finitePoissonVariance_nonneg p hp ht.le)

lemma lintegral_finitePoissonDispersion_ne_top (p : PMF ℝ) (hp : p.support.Finite) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (finitePoissonDispersion p hp t)) ≠ ∞ := by
  exact ne_of_lt ((finitePoissonDispersion_le_three_energy p hp).trans_lt
    (lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top (by norm_num) (finiteLaw_energy_ne_top p hp))))

lemma lintegral_time_finitePoissonVariance_ne_top (p : PMF ℝ) (hp : p.support.Finite) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t * finitePoissonVariance p hp t)) ≠ ∞ := by
  have hle : (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t * finitePoissonVariance p hp t)) ≤
      2 * ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t * finitePoissonVariance p hp t) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (show (1 : ℝ≥0∞) ≤ 2 by norm_num)
      (show 0 ≤ (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t * finitePoissonVariance p hp t))
        from zero_le)
  rw [finitePoissonVariance_energy_identity] at hle
  exact ne_of_lt (hle.trans_lt (lt_top_iff_ne_top.mpr
    (ENNReal.mul_ne_top (by norm_num) (finiteLaw_energy_ne_top p hp))))

theorem integrableOn_finitePoissonDispersion (p : PMF ℝ) (hp : p.support.Finite) :
    IntegrableOn (finitePoissonDispersion p hp) (Ioi 0) := by
  exact (lintegral_ofReal_ne_top_iff_integrable
    (continuous_finitePoissonDispersion p hp).aestronglyMeasurable
    (finitePoissonDispersion_ae_nonneg p hp)).mp
      (lintegral_finitePoissonDispersion_ne_top p hp)

theorem integrableOn_time_finitePoissonVariance (p : PMF ℝ) (hp : p.support.Finite) :
    IntegrableOn (fun t ↦ t * finitePoissonVariance p hp t) (Ioi 0) := by
  exact (lintegral_ofReal_ne_top_iff_integrable
    (continuous_id.mul (continuous_finitePoissonVariance p hp)).aestronglyMeasurable
    (time_finitePoissonVariance_ae_nonneg p hp)).mp
      (lintegral_time_finitePoissonVariance_ne_top p hp)

theorem integral_finitePoissonDispersion_le_integratedVariance
    (p : PMF ℝ) (hp : p.support.Finite) :
    (∫ t : ℝ in Ioi 0, finitePoissonDispersion p hp t) ≤
      2 * ∫ t : ℝ in Ioi 0, t * finitePoissonVariance p hp t := by
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (by norm_num) (lintegral_time_finitePoissonVariance_ne_top p hp))
    (finitePoissonDispersion_le_integratedVariance p hp)
  rw [integral_eq_lintegral_of_nonneg_ae (finitePoissonDispersion_ae_nonneg p hp)
      (integrableOn_finitePoissonDispersion p hp).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (time_finitePoissonVariance_ae_nonneg p hp)
      (integrableOn_time_finitePoissonVariance p hp).aestronglyMeasurable]
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] using h

theorem integral_finitePoissonVariance_energy_identity (p : PMF ℝ) (hp : p.support.Finite) :
    2 * (∫ t : ℝ in Ioi 0, t * finitePoissonVariance p hp t) =
      3 * (VarianceEnergy.energy p.toMeasure).toReal := by
  have h := congrArg ENNReal.toReal (finitePoissonVariance_energy_identity p hp)
  rw [integral_eq_lintegral_of_nonneg_ae (time_finitePoissonVariance_ae_nonneg p hp)
    (integrableOn_time_finitePoissonVariance p hp).aestronglyMeasurable]
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] using h

theorem integral_finitePoissonDispersion_le_three_energy (p : PMF ℝ) (hp : p.support.Finite) :
    (∫ t : ℝ in Ioi 0, finitePoissonDispersion p hp t) ≤
      3 * (VarianceEnergy.energy p.toMeasure).toReal := by
  exact (integral_finitePoissonDispersion_le_integratedVariance p hp).trans_eq
    (integral_finitePoissonVariance_energy_identity p hp)

end ExactOverlaps.Poisson
