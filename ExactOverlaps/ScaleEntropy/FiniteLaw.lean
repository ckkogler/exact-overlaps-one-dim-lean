/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.ScaleEntropy.Averaged

/-!
# The averaged chain rule for finite real laws

The entropy lost by quantization is the translation average of the ordinary
conditional entropy given the mesh label. This uses the actual finite law
and the same physical translation convention as the scale entropy.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace ExactOverlaps.ScaleEntropy

open Entropy

lemma law_eq_map_of_toMeasure_eq (μ : ProbabilityMeasure ℝ) (p : PMF ℝ)
    (hμp : (μ : Measure ℝ) = p.toMeasure) (r t : ℝ) :
    law μ r t = p.map (quantize r t) := by
  unfold law
  rw [PMF.toPMF_eq_iff_toMeasure_eq, ProbabilityMeasure.toMeasure_map,
    hμp, PMF.toMeasure_map (quantize r t) p (measurable_quantize r t)]

lemma finiteEntropy_sub_shiftedEntropy_eq_conditional (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (p : PMF ℝ) (hp : p.support.Finite)
    (hμp : (μ : Measure ℝ) = p.toMeasure) (r : ℝ) (hr : 0 < r) (t : ℝ) :
    finiteEntropy p hp - shiftedEntropy μ hμ r hr t =
      conditionalEntropy p hp (quantize r t) := by
  have h := conditionalEntropy_eq_entropy_sub p hp (quantize r t)
  simpa only [shiftedEntropy, law_eq_map_of_toMeasure_eq μ p hμp] using h.symm

lemma intervalIntegrable_finiteConditional (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (p : PMF ℝ) (hp : p.support.Finite)
    (hμp : (μ : Measure ℝ) = p.toMeasure) (r : ℝ) (hr : 0 < r) (u v : ℝ) :
    IntervalIntegrable (fun t ↦ conditionalEntropy p hp (quantize r t)) volume u v := by
  simp_rw [← finiteEntropy_sub_shiftedEntropy_eq_conditional μ hμ p hp hμp r hr]
  exact intervalIntegrable_const.sub (intervalIntegrable_shiftedEntropy μ hμ r hr u v)

/-- Exact averaged Shannon chain rule for a finite law and its shifted mesh labels. -/
theorem finiteEntropy_sub_entropy_eq_average_conditional (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (p : PMF ℝ) (hp : p.support.Finite)
    (hμp : (μ : Measure ℝ) = p.toMeasure) (r : ℝ) (hr : 0 < r) :
    finiteEntropy p hp - entropy μ hμ r hr =
      (∫ t in (0 : ℝ)..r, conditionalEntropy p hp (quantize r t)) / r := by
  simp_rw [← finiteEntropy_sub_shiftedEntropy_eq_conditional μ hμ p hp hμp r hr]
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    (intervalIntegrable_shiftedEntropy μ hμ r hr 0 r)]
  simp only [entropy, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  field_simp

end ExactOverlaps.ScaleEntropy
