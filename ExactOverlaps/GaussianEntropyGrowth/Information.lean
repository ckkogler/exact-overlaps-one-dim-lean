/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.GaussianScaleEntropy.FiniteMoments
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Countable entropy as an actual information integral

Summability first proves integrability of the information function. The
PMF expectation and the original quantized random variable then give the
same genuine integral, including zero-mass labels.
-/

@[expose] public section

noncomputable section
open MeasureTheory

namespace ExactOverlaps.GaussianEntropyGrowth

def information (p : PMF ℤ) (k : ℤ) : ℝ := -Real.log (p k).toReal

lemma information_nonneg (p : PMF ℤ) (k : ℤ) : 0 ≤ information p k := by
  apply neg_nonneg.mpr
  apply Real.log_nonpos ENNReal.toReal_nonneg
  simpa using ENNReal.toReal_mono ENNReal.one_ne_top (p.coe_le_one k)

lemma probability_mul_information (p : PMF ℤ) (k : ℤ) :
    (p k).toReal * information p k = Real.negMulLog (p k).toReal := by
  unfold information Real.negMulLog
  ring

lemma integrable_information (p : PMF ℤ)
    (hp : Summable (fun k ↦ Real.negMulLog (p k).toReal)) :
    Integrable (information p) p.toMeasure := by
  rw [← Measure.sum_smul_dirac p.toMeasure]
  apply integrable_sum_dirac (fun k ↦ measure_ne_top _ _)
  simpa only [p.toMeasure_apply_singleton _ (measurableSet_singleton _), Real.norm_eq_abs,
    abs_of_nonneg (information_nonneg p _), probability_mul_information] using hp

lemma integral_information (p : PMF ℤ)
    (hp : Summable (fun k ↦ Real.negMulLog (p k).toReal)) :
    (∫ k, information p k ∂p.toMeasure) = ∑' k, Real.negMulLog (p k).toReal := by
  rw [p.integral_eq_tsum _ (integrable_information p hp)]
  simp only [smul_eq_mul, probability_mul_information]

def cellInformation (μ : ProbabilityMeasure ℝ) (r t x : ℝ) : ℝ :=
  information (ScaleEntropy.law μ r t) (ScaleEntropy.quantize r t x)

lemma integrable_cellInformation (μ : ProbabilityMeasure ℝ) (r t : ℝ)
    (hs : Summable (GaussianScaleEntropy.cellTerm μ r t)) :
    Integrable (cellInformation μ r t) (μ : Measure ℝ) := by
  have h := integrable_information (ScaleEntropy.law μ r t) hs
  rw [ScaleEntropy.law_toMeasure] at h
  exact (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
    (ScaleEntropy.measurable_quantize r t).aemeasurable).mp h

lemma shiftedEntropy_eq_integral_information (μ : ProbabilityMeasure ℝ) (r t : ℝ)
    (hs : Summable (GaussianScaleEntropy.cellTerm μ r t)) :
    GaussianScaleEntropy.shiftedEntropy μ r t =
      ∫ x, cellInformation μ r t x ∂(μ : Measure ℝ) := by
  rw [GaussianScaleEntropy.shiftedEntropy_eq_tsum μ r t hs]
  simp only [GaussianScaleEntropy.cellTerm]
  rw [← integral_information (ScaleEntropy.law μ r t) hs,
    ScaleEntropy.law_toMeasure,
    integral_map (ScaleEntropy.measurable_quantize r t).aemeasurable
      (measurable_of_countable _).aestronglyMeasurable]
  rfl

end ExactOverlaps.GaussianEntropyGrowth
