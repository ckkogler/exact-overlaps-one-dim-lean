/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.ConvolutionDisintegration.Definition
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Measurability of the interval-width condition

A probability is carried by an interval of width r exactly when no two
rational half-lines separated by more than r both have positive mass.
This countable criterion proves measurability without an assumed measurable
choice of interval endpoints.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace ExactOverlaps.ConvolutionDisintegration

def rationalWidthCriterion (μ : ProbabilityMeasure ℝ) (r : ℝ) : Prop :=
  ∀ a b : ℚ, (a : ℝ) + r < b →
    (μ : Measure ℝ) (Iio (a : ℝ)) = 0 ∨ (μ : Measure ℝ) (Ioi (b : ℝ)) = 0

lemma HasIntervalWidth.rationalCriterion {μ : ProbabilityMeasure ℝ} {r : ℝ}
    (h : HasIntervalWidth μ r) : rationalWidthCriterion μ r := by
  obtain ⟨c, hc⟩ := h
  have hnull : (μ : Measure ℝ) (Icc c (c + r))ᶜ = 0 := by
    change (Icc c (c + r)) ∈ ae (μ : Measure ℝ) at hc
    exact mem_ae_iff.mp hc
  intro a b hab
  by_cases ha : (a : ℝ) ≤ c
  · left
    apply le_antisymm _ bot_le
    apply (measure_mono (show Iio (a : ℝ) ⊆ (Icc c (c + r))ᶜ from ?_)).trans_eq hnull
    intro x hx hxc
    exact (hx.trans_le ha).not_ge hxc.1
  · right
    have hb : c + r < (b : ℝ) := by linarith [lt_of_not_ge ha]
    apply le_antisymm _ bot_le
    apply (measure_mono (show Ioi (b : ℝ) ⊆ (Icc c (c + r))ᶜ from ?_)).trans_eq hnull
    intro x hx hxc
    exact (hb.trans hx).not_ge hxc.2

lemma rationalWidthCriterion.support_sub_le {μ : ProbabilityMeasure ℝ} {r : ℝ}
    (h : rationalWidthCriterion μ r) {x y : ℝ}
    (hx : x ∈ (μ : Measure ℝ).support) (hy : y ∈ (μ : Measure ℝ).support) : y - x ≤ r := by
  by_contra hxy
  have hgap : x < y - r := by linarith
  obtain ⟨a, hxa, hay⟩ := exists_rat_btwn hgap
  have hagap : (a : ℝ) + r < y := by linarith
  obtain ⟨b, hab, hby⟩ := exists_rat_btwn hagap
  have hleft : 0 < (μ : Measure ℝ) (Iio (a : ℝ)) :=
    ((μ : Measure ℝ).mem_support_iff_forall x).mp hx _ (Iio_mem_nhds hxa)
  have hright : 0 < (μ : Measure ℝ) (Ioi (b : ℝ)) :=
    ((μ : Measure ℝ).mem_support_iff_forall y).mp hy _ (Ioi_mem_nhds hby)
  rcases h a b hab with hz | hz
  · exact hleft.ne' hz
  · exact hright.ne' hz

lemma rationalWidthCriterion.hasIntervalWidth {μ : ProbabilityMeasure ℝ} {r : ℝ}
    (h : rationalWidthCriterion μ r) : HasIntervalWidth μ r := by
  have hae : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ (μ : Measure ℝ).support :=
    mem_ae_iff.mpr (μ : Measure ℝ).support_mem_ae
  obtain ⟨x, hx⟩ := hae.exists
  have hne : (μ : Measure ℝ).support.Nonempty := ⟨x, hx⟩
  have hb : BddBelow (μ : Measure ℝ).support := by
    refine ⟨x - r, ?_⟩
    intro y hy
    have hxy := h.support_sub_le hy hx
    linarith
  refine ⟨sInf (μ : Measure ℝ).support, ?_⟩
  filter_upwards [hae] with y hy
  refine ⟨csInf_le hb hy, ?_⟩
  have hlo : y - r ≤ sInf (μ : Measure ℝ).support := by
    apply le_csInf hne
    intro z hz
    have hzy := h.support_sub_le hz hy
    linarith
  linarith

lemma hasIntervalWidth_iff_rationalCriterion (μ : ProbabilityMeasure ℝ) (r : ℝ) :
    HasIntervalWidth μ r ↔ rationalWidthCriterion μ r :=
  ⟨HasIntervalWidth.rationalCriterion, rationalWidthCriterion.hasIntervalWidth⟩

lemma measurableSet_hasIntervalWidth (r : ℝ) :
    MeasurableSet {μ : ProbabilityMeasure ℝ | HasIntervalWidth μ r} := by
  simp_rw [hasIntervalWidth_iff_rationalCriterion, rationalWidthCriterion, ofPred_forall]
  apply MeasurableSet.iInter
  intro a
  apply MeasurableSet.iInter
  intro b
  apply MeasurableSet.iInter
  intro _
  apply MeasurableSet.union
  · exact ((Measure.measurable_coe measurableSet_Iio).comp measurable_subtype_coe)
      (measurableSet_singleton 0)
  · exact ((Measure.measurable_coe measurableSet_Ioi).comp measurable_subtype_coe)
      (measurableSet_singleton 0)

end ExactOverlaps.ConvolutionDisintegration
