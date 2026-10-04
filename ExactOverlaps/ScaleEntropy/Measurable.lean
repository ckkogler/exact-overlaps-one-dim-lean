/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.ScaleEntropy.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Measurability and local integrability of shifted entropy

Each cell mass is measurable in the physical translation. Expressing entropy
as its countable sum proves measurability without choosing a support depending
measurably on the translation. A common finite label set on every compact
translation interval supplies integrability.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ExactOverlaps.ScaleEntropy

open Entropy

lemma measurable_law_apply (μ : ProbabilityMeasure ℝ) (r : ℝ) (k : ℤ) :
    Measurable (fun t ↦ law μ r t k) := by
  have hs : MeasurableSet {p : ℝ × ℝ | quantize r p.1 p.2 = k} :=
    (measurable_quantize_joint r) (measurableSet_singleton k)
  simpa only [law_apply, Set.preimage_ofPred_eq] using
    (measurable_measure_prodMk_left (ν := (μ : Measure ℝ)) hs)

lemma shiftedEntropy_eq_tsum (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ)
    (r : ℝ) (hr : 0 < r) (t : ℝ) :
    shiftedEntropy μ hμ r hr t = ∑' k : ℤ, Real.negMulLog (law μ r t k).toReal := by
  classical
  symm
  apply tsum_eq_sum
  intro k hk
  have hz : law μ r t k = 0 := by simpa using hk
  simp [hz]

@[fun_prop] lemma measurable_shiftedEntropy (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (r : ℝ) (hr : 0 < r) :
    Measurable (shiftedEntropy μ hμ r hr) := by
  have hm : Measurable (fun t ↦ ∑' k : ℤ, Real.negMulLog (law μ r t k).toReal) :=
    Measurable.tsum (fun k ↦ Real.continuous_negMulLog.measurable.comp
      (measurable_law_apply μ r k).ennreal_toReal)
  simpa only [← shiftedEntropy_eq_tsum μ hμ r hr] using hm

lemma law_support_subset_uniform (μ : ProbabilityMeasure ℝ) {r : ℝ} (hr : 0 < r)
    {a b u v t : ℝ} (hμ : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc a b)
    (ht : t ∈ Icc u v) :
    (law μ r t).support ⊆ Icc (quantize r u a) (quantize r v b) := by
  intro k hk
  have h := law_support_subset μ hr t hμ hk
  exact ⟨le_trans (Int.floor_mono (div_le_div_of_nonneg_right
      (add_le_add le_rfl ht.1) hr.le)) h.1,
    le_trans h.2 (Int.floor_mono (div_le_div_of_nonneg_right
      (add_le_add le_rfl ht.2) hr.le))⟩

lemma shiftedEntropy_le_uniform_card (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) {r : ℝ} (hr : 0 < r) {a b u v t : ℝ}
    (hab : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc a b) (ht : t ∈ Icc u v) :
    shiftedEntropy μ hμ r hr t ≤
      (Finset.Icc (quantize r u a) (quantize r v b)).card := by
  have hsub : (law_support_finite μ hμ hr t).toFinset ⊆
      Finset.Icc (quantize r u a) (quantize r v b) := by
    intro k hk
    exact Finset.mem_Icc.mpr (law_support_subset_uniform μ hr hab ht (by simpa using hk))
  exact (finiteEntropy_le_log_card _ _).trans
    ((Real.log_le_self (Nat.cast_nonneg _)).trans (by exact_mod_cast Finset.card_le_card hsub))

lemma integrableOn_shiftedEntropy_Icc (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (r : ℝ) (hr : 0 < r) (u v : ℝ) :
    IntegrableOn (shiftedEntropy μ hμ r hr) (Icc u v) := by
  have hbounded := hμ
  obtain ⟨a, b, hab⟩ := hbounded
  apply Measure.integrableOn_of_bounded (measure_Icc_lt_top.ne)
    (measurable_shiftedEntropy μ hμ r hr).aestronglyMeasurable
    (M := (Finset.Icc (quantize r u a) (quantize r v b)).card)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (shiftedEntropy_nonneg μ hμ r hr t)]
  exact shiftedEntropy_le_uniform_card μ hμ hr hab ht

lemma intervalIntegrable_shiftedEntropy (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (r : ℝ) (hr : 0 < r) (u v : ℝ) :
    IntervalIntegrable (shiftedEntropy μ hμ r hr) volume u v := by
  exact (integrableOn_shiftedEntropy_Icc μ hμ r hr (min u v) (max u v)).intervalIntegrable

end ExactOverlaps.ScaleEntropy
