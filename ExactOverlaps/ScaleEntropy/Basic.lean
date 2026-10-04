/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.Entropy.Dyadic

/-!
# Entropy at arbitrary positive mesh size

The quantizer is `floor ((x + t) / r)`, with physical translation `t`.
Its entropy is the entropy of the actual push-forward probability law.
Bounded support supplies finiteness without excluding atoms on cell boundaries.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace ExactOverlaps.ScaleEntropy

open Entropy

/-- Half-open mesh label, with a translation in physical coordinates. -/
def quantize (r t x : ℝ) : ℤ := ⌊(x + t) / r⌋

@[fun_prop] lemma measurable_quantize (r t : ℝ) : Measurable (quantize r t) := by
  unfold quantize
  fun_prop

@[fun_prop] lemma measurable_quantize_joint (r : ℝ) :
    Measurable (fun p : ℝ × ℝ ↦ quantize r p.1 p.2) := by
  unfold quantize
  fun_prop

lemma quantize_mono {r : ℝ} (hr : 0 < r) (t : ℝ) : Monotone (quantize r t) := by
  intro x y hxy
  exact Int.floor_mono (div_le_div_of_nonneg_right (add_le_add hxy le_rfl) hr.le)

/-- The probability mass function of the mesh label. -/
def law (μ : ProbabilityMeasure ℝ) (r t : ℝ) : PMF ℤ :=
  (μ.map (quantize r t)).toMeasure.toPMF

lemma law_apply (μ : ProbabilityMeasure ℝ) (r t : ℝ) (k : ℤ) :
    law μ r t k = (μ : Measure ℝ) {x | quantize r t x = k} := by
  rw [law, Measure.toPMF_apply,
    ProbabilityMeasure.map_apply' μ (measurable_quantize r t).aemeasurable
      (measurableSet_singleton k)]
  rfl

lemma law_toMeasure (μ : ProbabilityMeasure ℝ) (r t : ℝ) :
    (law μ r t).toMeasure = (μ : Measure ℝ).map (quantize r t) := by
  simp [law]

lemma law_support_subset (μ : ProbabilityMeasure ℝ) {r : ℝ} (hr : 0 < r)
    (t : ℝ) {a b : ℝ} (hμ : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc a b) :
    (law μ r t).support ⊆ Icc (quantize r t a) (quantize r t b) := by
  intro k hk
  by_contra hnot
  have hzero : (μ : Measure ℝ) {x | quantize r t x = k} = 0 := by
    apply measure_mono_null (t := {x | x ∉ Icc a b})
    · intro x hx hxab
      apply hnot
      rw [← hx]
      exact ⟨quantize_mono hr t hxab.1, quantize_mono hr t hxab.2⟩
    · exact ae_iff.mp hμ
  exact hk (by rw [law_apply, hzero])

lemma law_support_finite (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ)
    {r : ℝ} (hr : 0 < r) (t : ℝ) : (law μ r t).support.Finite := by
  obtain ⟨a, b, hab⟩ := hμ
  exact (Set.finite_Icc (quantize r t a) (quantize r t b)).subset
    (law_support_subset μ hr t hab)

/-- Natural-logarithmic entropy of the shifted mesh partition. -/
def shiftedEntropy (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ)
    (r : ℝ) (hr : 0 < r) (t : ℝ) : ℝ :=
  finiteEntropy (law μ r t) (law_support_finite μ hμ hr t)

lemma shiftedEntropy_nonneg (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ)
    (r : ℝ) (hr : 0 < r) (t : ℝ) : 0 ≤ shiftedEntropy μ hμ r hr t :=
  finiteEntropy_nonneg _ _

lemma quantize_add_period {r : ℝ} (hr : r ≠ 0) (t x : ℝ) :
    quantize r (t + r) x = quantize r t x + 1 := by
  unfold quantize
  have heq : (x + (t + r)) / r = (x + t) / r + 1 := by field_simp; ring
  rw [heq, Int.floor_add_one]

lemma law_add_period (μ : ProbabilityMeasure ℝ) {r : ℝ} (hr : r ≠ 0) (t : ℝ) :
    law μ r (t + r) = (law μ r t).map (fun k ↦ k + 1) := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map _ _ (measurable_of_countable _), law_toMeasure,
    law_toMeasure, Measure.map_map (measurable_of_countable _) (measurable_quantize r t)]
  congr 1
  funext x
  exact quantize_add_period hr t x

lemma shiftedEntropy_periodic (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ)
    (r : ℝ) (hr : 0 < r) : Function.Periodic (shiftedEntropy μ hμ r hr) r := by
  intro t
  simpa only [shiftedEntropy, law_add_period μ hr.ne'] using
    (finiteEntropy_map_of_injective (law μ r t) (law_support_finite μ hμ hr t)
      (f := fun k : ℤ ↦ k + 1) (fun a b h ↦ add_right_cancel h))

/-- Coarse labels are an integer quotient of fine labels at integer-related scales. -/
lemma quantize_nat_mul (r t x : ℝ) (C : ℕ) :
    quantize ((C : ℝ) * r) t x = quantize r t x / C := by
  unfold quantize
  rw [← Int.floor_div_natCast]
  congr 1
  rw [div_div, mul_comm r (C : ℝ)]

lemma law_map_div (μ : ProbabilityMeasure ℝ) (r t : ℝ) (C : ℕ) :
    (law μ r t).map (fun k ↦ k / (C : ℤ)) = law μ ((C : ℝ) * r) t := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map _ _ (measurable_of_countable _), law_toMeasure,
    law_toMeasure, Measure.map_map (measurable_of_countable _) (measurable_quantize r t)]
  congr 1
  funext x
  exact (quantize_nat_mul r t x C).symm

end ExactOverlaps.ScaleEntropy
