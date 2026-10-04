/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.GaussianScaleEntropy.Scaling

/-!
# Entropy finiteness at every positive physical scale

An actual finite second moment guarantees summability of every cell
entropy sum occurring in the translation average and integrability of
that average. Thus the real entropy used below never relies on the
totalized value of a divergent sum or a nonintegrable integral.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace ExactOverlaps.GaussianScaleEntropy

lemma div_mem_unit_interval {r t : ℝ} (hr : 0 < r) (ht : t ∈ Icc 0 r) :
    t / r ∈ Icc (0 : ℝ) 1 :=
  ⟨div_nonneg ht.1 hr.le, (div_le_one hr).mpr ht.2⟩

lemma summable_cellTerm_at_scale (μ : ProbabilityMeasure ℝ)
    (hμ : Integrable (fun x : ℝ ↦ x ^ 2) (μ : Measure ℝ))
    {r t : ℝ} (hr : 0 < r) (ht : t ∈ Icc 0 r) : Summable (cellTerm μ r t) := by
  let ρ := normalize μ r
  let B := ∫ x, x ^ 2 ∂(ρ : Measure ℝ)
  have hB : 0 ≤ B := integral_nonneg (fun x ↦ sq_nonneg x)
  have h := summable_cellTerm ρ (integrable_sq_normalize μ hμ r) hB le_rfl
    (div_mem_unit_interval hr ht)
  change Summable (fun k ↦ cellTerm ρ 1 (t / r) k) at h
  change Summable (fun k ↦ cellTerm μ r t k)
  simpa only [ρ, cellTerm, law_normalize μ hr.ne', mul_div_cancel₀ t hr.ne'] using h

lemma cellEntropy_ne_top_at_scale (μ : ProbabilityMeasure ℝ)
    (hμ : Integrable (fun x : ℝ ↦ x ^ 2) (μ : Measure ℝ))
    {r t : ℝ} (hr : 0 < r) (ht : t ∈ Icc 0 r) : cellEntropy μ r t ≠ ∞ :=
  cellEntropy_ne_top_of_summable μ r t (summable_cellTerm_at_scale μ hμ hr ht)

lemma shiftedEntropy_le_scaled_envelope (μ : ProbabilityMeasure ℝ)
    (hμ : Integrable (fun x : ℝ ↦ x ^ 2) (μ : Measure ℝ))
    {r t : ℝ} (hr : 0 < r) (ht : t ∈ Icc 0 r) :
    shiftedEntropy μ r t ≤
      ∑' k : ℤ, entropyEnvelope (∫ x, x ^ 2 ∂(normalize μ r : Measure ℝ)) k := by
  have h := shiftedEntropy_le_envelope_sum (normalize μ r) (integrable_sq_normalize μ hμ r)
    (integral_nonneg (fun x ↦ sq_nonneg x)) le_rfl (div_mem_unit_interval hr ht)
  simpa only [shiftedEntropy_normalize μ hr.ne', mul_div_cancel₀ t hr.ne'] using h

lemma integrableOn_shiftedEntropy_at_scale (μ : ProbabilityMeasure ℝ)
    (hμ : Integrable (fun x : ℝ ↦ x ^ 2) (μ : Measure ℝ))
    {r : ℝ} (hr : 0 < r) : IntegrableOn (shiftedEntropy μ r) (Icc 0 r) := by
  apply Measure.integrableOn_of_bounded (measure_Icc_lt_top.ne)
    (measurable_shiftedEntropy μ r).aestronglyMeasurable
    (M := ∑' k : ℤ, entropyEnvelope (∫ x, x ^ 2 ∂(normalize μ r : Measure ℝ)) k)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (shiftedEntropy_nonneg μ r t)]
  exact shiftedEntropy_le_scaled_envelope μ hμ hr ht

lemma intervalIntegrable_shiftedEntropy_at_scale (μ : ProbabilityMeasure ℝ)
    (hμ : Integrable (fun x : ℝ ↦ x ^ 2) (μ : Measure ℝ))
    {r : ℝ} (hr : 0 < r) : IntervalIntegrable (shiftedEntropy μ r) volume 0 r := by
  apply IntegrableOn.intervalIntegrable
  simpa only [uIcc_of_le hr.le] using integrableOn_shiftedEntropy_at_scale μ hμ hr

end ExactOverlaps.GaussianScaleEntropy
