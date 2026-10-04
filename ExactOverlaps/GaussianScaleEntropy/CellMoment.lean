/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.GaussianScaleEntropy.Basic

/-!
# Quadratic decay of shifted unit-cell probabilities

The quantizer label differs from the sampled value by at most one for a
translation in the unit interval. Markov's inequality therefore gives a
cell-probability bound uniform in that translation from the actual second
moment of the law.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set

namespace ExactOverlaps.GaussianScaleEntropy

lemma abs_label_le {t x : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (k : ℤ)
    (hk : ScaleEntropy.quantize 1 t x = k) : |(k : ℝ)| ≤ |x| + 1 := by
  have h := Int.floor_eq_iff.mp hk
  simp only [div_one] at h
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le x, h.2, ht.1]
  · linarith [le_abs_self x, h.1, ht.2]

lemma label_sq_le {t x : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (k : ℤ)
    (hk : ScaleEntropy.quantize 1 t x = k) : (k : ℝ) ^ 2 ≤ 2 * x ^ 2 + 2 := by
  have h := abs_label_le ht k hk
  have ha := abs_nonneg (k : ℝ)
  have hx := abs_nonneg x
  nlinarith [sq_abs (k : ℝ), sq_abs x, sq_nonneg (|x| - 1)]

lemma sq_mul_cellProbability_le (μ : ProbabilityMeasure ℝ)
    (hμ : Integrable (fun x : ℝ ↦ x ^ 2) (μ : Measure ℝ))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (k : ℤ) :
    (k : ℝ) ^ 2 * (ScaleEntropy.law μ 1 t k).toReal ≤
      2 * (∫ x, x ^ 2 ∂(μ : Measure ℝ)) + 2 := by
  have hsub : {x | ScaleEntropy.quantize 1 t x = k} ⊆
      {x : ℝ | (k : ℝ) ^ 2 ≤ 2 * x ^ 2 + 2} := fun _ hx ↦ label_sq_le ht k hx
  rw [ScaleEntropy.law_apply]
  change (k : ℝ) ^ 2 * (μ : Measure ℝ).real {x | ScaleEntropy.quantize 1 t x = k} ≤ _
  calc
    _ ≤ (k : ℝ) ^ 2 * (μ : Measure ℝ).real {x : ℝ | (k : ℝ) ^ 2 ≤ 2 * x ^ 2 + 2} :=
      mul_le_mul_of_nonneg_left (measureReal_mono hsub) (sq_nonneg _)
    _ ≤ ∫ x, (2 * x ^ 2 + 2) ∂(μ : Measure ℝ) :=
      mul_meas_ge_le_integral_of_nonneg
        (Filter.Eventually.of_forall (fun x : ℝ ↦ show 0 ≤ 2 * x ^ 2 + 2 by positivity))
        ((hμ.const_mul 2).add (integrable_const 2)) _
    _ = _ := by
      rw [integral_add (hμ.const_mul 2) (integrable_const 2), integral_const_mul,
        integral_const]
      simp

lemma cellProbability_le_secondMoment (μ : ProbabilityMeasure ℝ)
    (hμ : Integrable (fun x : ℝ ↦ x ^ 2) (μ : Measure ℝ))
    {B t : ℝ} (hB : (∫ x, x ^ 2 ∂(μ : Measure ℝ)) ≤ B)
    (ht : t ∈ Icc (0 : ℝ) 1) (k : ℤ) (hk : k ≠ 0) :
    (ScaleEntropy.law μ 1 t k).toReal ≤ (2 * B + 2) / (k : ℝ) ^ 2 := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  apply (le_div_iff₀ (sq_pos_of_ne_zero hkR)).mpr
  have h := sq_mul_cellProbability_le μ hμ ht k
  nlinarith

end ExactOverlaps.GaussianScaleEntropy
