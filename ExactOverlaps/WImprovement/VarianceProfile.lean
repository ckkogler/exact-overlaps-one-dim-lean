/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.VarianceEnergy.FiniteEnergy
public import ExactOverlaps.VarianceEnergy.Measurable
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Actual real variance profiles and logarithmic change of variables

Finite extended variance energy implies integrability before conversion to
ordinary real integrals. The truncated logarithmic profile integrates to
the exact energy below the given physical scale.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace ExactOverlaps.WImprovement

open VarianceEnergy

def varianceProfile (μ : Measure ℝ) (r : ℝ) : ℝ :=
  (normalizedLocalVariance μ r).toReal

def varianceDensity (μ : Measure ℝ) (r : ℝ) : ℝ :=
  (normalizedLocalVariance μ r * ENNReal.ofReal (1 / r)).toReal

def logVarianceProfile (μ : Measure ℝ) (R u : ℝ) : ℝ :=
  if Real.exp u < R then varianceProfile μ (Real.exp u) else 0

lemma varianceProfile_nonneg (μ : Measure ℝ) (r : ℝ) : 0 ≤ varianceProfile μ r :=
  ENNReal.toReal_nonneg

lemma varianceProfile_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 < r) : varianceProfile μ r ≤ 1 := by
  simpa only [varianceProfile, ENNReal.toReal_one] using
    ENNReal.toReal_mono ENNReal.one_ne_top (normalizedLocalVariance_le_one μ hr)

lemma measurable_varianceDensity (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Measurable (varianceDensity μ) :=
  ((measurable_normalizedLocalVariance μ).mul (by fun_prop)).ennreal_toReal

lemma varianceDensity_eq (μ : Measure ℝ) {r : ℝ} (hr : 0 < r) :
    varianceDensity μ r = varianceProfile μ r / r := by
  rw [varianceDensity, varianceProfile, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / r)]
  ring

lemma integrableOn_varianceDensity (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hE : energy μ ≠ ∞) : IntegrableOn (varianceDensity μ) (Ioi 0) := by
  apply integrable_toReal_of_lintegral_ne_top
  · exact ((measurable_normalizedLocalVariance μ).mul (by fun_prop)).aemeasurable
  · exact hE

lemma integral_varianceDensity_below (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (_hE : energy μ ≠ ∞) (R : ℝ) :
    (∫ r in Ioo (0 : ℝ) R, varianceDensity μ r) = (energyBelow μ R).toReal := by
  apply integral_toReal
  · exact ((measurable_normalizedLocalVariance μ).mul (by fun_prop)).aemeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    apply ENNReal.mul_lt_top
    · exact (normalizedLocalVariance_le_one μ hr.1).trans_lt ENNReal.one_lt_top
    · exact ENNReal.ofReal_lt_top

lemma exp_mul_truncated_density (μ : Measure ℝ) (R u : ℝ) :
    Real.exp u * (Iio R).indicator (varianceDensity μ) (Real.exp u) =
      logVarianceProfile μ R u := by
  by_cases h : Real.exp u < R
  · rw [Set.indicator_of_mem (show Real.exp u ∈ Iio R from h)]
    simp only [logVarianceProfile, ite_eq_left h, varianceDensity_eq μ (Real.exp_pos u)]
    field_simp
  · simp only [Set.indicator_of_notMem (show Real.exp u ∉ Iio R from h),
      logVarianceProfile, ite_eq_right h, mul_zero]

lemma integrable_logVarianceProfile (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hE : energy μ ≠ ∞) (R : ℝ) : Integrable (logVarianceProfile μ R) := by
  have hi : IntegrableOn ((Iio R).indicator (varianceDensity μ)) (Ioi 0) :=
    (integrableOn_varianceDensity μ hE).indicator measurableSet_Iio
  have h := (integrable_comp_exp _).mpr hi
  simpa only [smul_eq_mul, exp_mul_truncated_density] using h

lemma integral_logVarianceProfile (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hE : energy μ ≠ ∞) (R : ℝ) :
    (∫ u, logVarianceProfile μ R u) = (energyBelow μ R).toReal := by
  have h := integral_comp_exp ((Iio R).indicator (varianceDensity μ))
  simp only [smul_eq_mul, exp_mul_truncated_density] at h
  rw [h, integral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio]
  have he : Iio R ∩ Ioi (0 : ℝ) = Ioo 0 R := by ext x; simp [and_comm]
  rw [he]
  exact integral_varianceDensity_below μ hE R

lemma logVarianceProfile_nonneg (μ : Measure ℝ) (R u : ℝ) :
    0 ≤ logVarianceProfile μ R u := by
  unfold logVarianceProfile
  split_ifs
  · exact varianceProfile_nonneg _ _
  · exact le_rfl

lemma logVarianceProfile_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] (R u : ℝ) :
    logVarianceProfile μ R u ≤ 1 := by
  unfold logVarianceProfile
  split_ifs
  · exact varianceProfile_le_one μ (Real.exp_pos u)
  · norm_num

lemma logVarianceProfile_eq_zero_of_cutoffs (μ : Measure ℝ) {δ R : ℝ}
    (hδ : 0 < δ) (hR : 0 < R)
    (hvanish : ∀ r ≤ δ, normalizedLocalVariance μ r = 0) (u : ℝ)
    (hu : u ≤ Real.log δ ∨ Real.log R ≤ u) : logVarianceProfile μ R u = 0 := by
  rcases hu with hu | hu
  · have he : Real.exp u ≤ δ := (Real.exp_le_exp.mpr hu).trans_eq (Real.exp_log hδ)
    unfold logVarianceProfile varianceProfile
    rw [hvanish _ he, ENNReal.toReal_zero]
    split_ifs <;> rfl
  · have he : R ≤ Real.exp u := (Real.exp_log hR).symm.trans_le (Real.exp_le_exp.mpr hu)
    exact ite_eq_right (not_lt_of_ge he)

end ExactOverlaps.WImprovement
