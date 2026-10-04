/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.GaussianScaleEntropy.CellMoment
public import ExactOverlaps.GaussianScaleEntropy.PowerBound

/-!
# A uniform summable envelope for finite-second-moment entropy

The zero cell is bounded by one and the remaining cells by a fixed
summable power sequence. The bound is uniform over all shifts in the
unit interval and all probability laws with the prescribed moment bound.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace ExactOverlaps.GaussianScaleEntropy

def entropyEnvelope (B : ℝ) (k : ℤ) : ℝ :=
  (if k = 0 then 1 else 0) +
    4 * (2 * B + 2) ^ (3 / 4 : ℝ) * |(k : ℝ)| ^ (-(3 / 2 : ℝ))

lemma entropyEnvelope_nonneg {B : ℝ} (hB : 0 ≤ B) (k : ℤ) :
    0 ≤ entropyEnvelope B k := by
  unfold entropyEnvelope
  positivity

lemma summable_entropyEnvelope (B : ℝ) : Summable (entropyEnvelope B) := by
  have hzero : Summable (fun k : ℤ ↦ if k = 0 then (1 : ℝ) else 0) := by
    apply summable_of_ne_finset_zero (s := {0})
    intro k hk
    simp only [Finset.mem_singleton] at hk
    simp [hk]
  exact hzero.add (summable_entropy_power.mul_left _)

lemma rpow_quadratic_decay {C : ℝ} (hC : 0 ≤ C) (k : ℤ) :
    (C / (k : ℝ) ^ 2) ^ (3 / 4 : ℝ) =
      C ^ (3 / 4 : ℝ) * |(k : ℝ)| ^ (-(3 / 2 : ℝ)) := by
  rw [← sq_abs (k : ℝ), Real.div_rpow hC (sq_nonneg _),
    ← Real.rpow_natCast_mul (abs_nonneg (k : ℝ))]
  norm_num
  rw [Real.rpow_neg (abs_nonneg (k : ℝ)), div_eq_mul_inv]

lemma cellTerm_le_entropyEnvelope (μ : ProbabilityMeasure ℝ)
    (hμ : Integrable (fun x : ℝ ↦ x ^ 2) (μ : Measure ℝ))
    {B t : ℝ} (hB0 : 0 ≤ B) (hB : (∫ x, x ^ 2 ∂(μ : Measure ℝ)) ≤ B)
    (ht : t ∈ Icc (0 : ℝ) 1) (k : ℤ) :
    cellTerm μ 1 t k ≤ entropyEnvelope B k := by
  by_cases hk : k = 0
  · subst k
    simpa [entropyEnvelope] using cellTerm_le_one μ 1 t 0
  have hp := cellProbability_le_secondMoment μ hμ hB ht k hk
  have hpow := Real.rpow_le_rpow ENNReal.toReal_nonneg hp (by norm_num : (0 : ℝ) ≤ 3 / 4)
  rw [rpow_quadratic_decay (by positivity : 0 ≤ 2 * B + 2) k] at hpow
  have hn := negMulLog_le_four_rpow (ENNReal.toReal_nonneg
    (a := ScaleEntropy.law μ 1 t k))
  change cellTerm μ 1 t k ≤ _ at hn
  unfold entropyEnvelope
  rw [ite_eq_right hk, zero_add]
  exact hn.trans (by nlinarith)

lemma summable_cellTerm (μ : ProbabilityMeasure ℝ)
    (hμ : Integrable (fun x : ℝ ↦ x ^ 2) (μ : Measure ℝ))
    {B t : ℝ} (hB0 : 0 ≤ B) (hB : (∫ x, x ^ 2 ∂(μ : Measure ℝ)) ≤ B)
    (ht : t ∈ Icc (0 : ℝ) 1) : Summable (cellTerm μ 1 t) :=
  Summable.of_nonneg_of_le (cellTerm_nonneg μ 1 t)
    (cellTerm_le_entropyEnvelope μ hμ hB0 hB ht) (summable_entropyEnvelope B)

lemma cellEntropy_ne_top (μ : ProbabilityMeasure ℝ)
    (hμ : Integrable (fun x : ℝ ↦ x ^ 2) (μ : Measure ℝ))
    {B t : ℝ} (hB0 : 0 ≤ B) (hB : (∫ x, x ^ 2 ∂(μ : Measure ℝ)) ≤ B)
    (ht : t ∈ Icc (0 : ℝ) 1) : cellEntropy μ 1 t ≠ ∞ :=
  cellEntropy_ne_top_of_summable μ 1 t (summable_cellTerm μ hμ hB0 hB ht)

lemma shiftedEntropy_le_envelope_sum (μ : ProbabilityMeasure ℝ)
    (hμ : Integrable (fun x : ℝ ↦ x ^ 2) (μ : Measure ℝ))
    {B t : ℝ} (hB0 : 0 ≤ B) (hB : (∫ x, x ^ 2 ∂(μ : Measure ℝ)) ≤ B)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    shiftedEntropy μ 1 t ≤ ∑' k : ℤ, entropyEnvelope B k := by
  rw [shiftedEntropy_eq_tsum μ 1 t (summable_cellTerm μ hμ hB0 hB ht)]
  exact Summable.tsum_le_tsum (cellTerm_le_entropyEnvelope μ hμ hB0 hB ht)
    (summable_cellTerm μ hμ hB0 hB ht) (summable_entropyEnvelope B)

lemma integrableOn_shiftedEntropy_unit (μ : ProbabilityMeasure ℝ)
    (hμ : Integrable (fun x : ℝ ↦ x ^ 2) (μ : Measure ℝ)) :
    IntegrableOn (shiftedEntropy μ 1) (Icc (0 : ℝ) 1) := by
  let B := ∫ x, x ^ 2 ∂(μ : Measure ℝ)
  have hB : 0 ≤ B := integral_nonneg (fun x ↦ sq_nonneg x)
  apply Measure.integrableOn_of_bounded (measure_Icc_lt_top.ne)
    (measurable_shiftedEntropy μ 1).aestronglyMeasurable
    (M := ∑' k : ℤ, entropyEnvelope B k)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (shiftedEntropy_nonneg μ 1 t)]
  exact shiftedEntropy_le_envelope_sum μ hμ hB le_rfl ht

end ExactOverlaps.GaussianScaleEntropy
