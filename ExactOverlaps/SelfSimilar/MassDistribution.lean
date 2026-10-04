module

public import ExactOverlaps.SelfSimilar.Dimension
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Topology.MetricSpace.Bounded

/-!
Mass distribution estimates using outer-measure restriction. The good
set need not be measurable: this matters when a uniform ball bound is
defined by a condition on every sufficiently small real radius.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace ExactOverlaps

theorem outer_restrict_le_hausdorff (μ : Measure ℝ) (E : Set ℝ) (s : ℝ)
    {ε : ℝ≥0∞} (hε : 0 < ε)
    (hbound : ∀ A : Set ℝ, Metric.ediam A ≤ ε → μ (A ∩ E) ≤ Metric.ediam A ^ s)
    (A : Set ℝ) : μ (A ∩ E) ≤ Measure.hausdorffMeasure s A := by
  let κ := μ.toOuterMeasure.restrict E
  have hpre : κ ≤ OuterMeasure.mkMetric'.pre (fun B : Set ℝ ↦ Metric.ediam B ^ s) ε := by
    apply OuterMeasure.mkMetric'.le_pre.mpr
    intro B hB
    simpa only [κ, OuterMeasure.restrict_apply, Measure.coe_toOuterMeasure] using hbound B hB
  have hmetric : κ ≤ (OuterMeasure.mkMetric (fun r ↦ r ^ s) : OuterMeasure ℝ) :=
    hpre.trans (le_iSup_of_le ε (le_iSup_of_le hε le_rfl))
  have hh := hmetric A
  simpa only [κ, OuterMeasure.restrict_apply, Measure.coe_toOuterMeasure,
    OuterMeasure.coe_mkMetric, Measure.hausdorffMeasure] using hh

theorem restricted_mass_le_hausdorff_of_ball_bound (μ : Measure ℝ) (E : Set ℝ) (s : ℝ)
    {ε : ℝ} (hε : 0 < ε)
    (hball : ∀ x ∈ E, ∀ r : ℝ, 0 ≤ r → r ≤ ε →
      μ (closedBall x r) ≤ (ENNReal.ofReal r) ^ s) (A : Set ℝ) :
    μ (A ∩ E) ≤ Measure.hausdorffMeasure s A := by
  apply outer_restrict_le_hausdorff μ E s (ENNReal.ofReal_pos.mpr hε)
  intro B hB
  by_cases hBE : (B ∩ E).Nonempty
  · obtain ⟨x, hxB, hxE⟩ := hBE
    have hfin : Metric.ediam B ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hB
    have hdε : (Metric.ediam B).toReal ≤ ε := ENNReal.toReal_le_of_le_ofReal hε.le hB
    have hsub : B ∩ E ⊆ closedBall x (Metric.ediam B).toReal := by
      intro y hy
      exact dist_le_diam_of_mem' hfin hy.1 hxB
    calc
      μ (B ∩ E) ≤ μ (closedBall x (Metric.ediam B).toReal) := measure_mono hsub
      _ ≤ (ENNReal.ofReal (Metric.ediam B).toReal) ^ s :=
        hball x hxE _ ENNReal.toReal_nonneg hdε
      _ = Metric.ediam B ^ s := by rw [ENNReal.ofReal_toReal hfin]
  · simp only [Set.not_nonempty_iff_eq_empty.mp hBE, measure_empty, zero_le]

theorem lowerHausdorffDimension_ge_of_ball_good_sets (μ : Measure ℝ) (s : ℝ≥0)
    (E : ℕ → Set ℝ) (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    (hball : ∀ n, ∀ x ∈ E n, ∀ r : ℝ, 0 ≤ r → r ≤ ε n →
      μ (closedBall x r) ≤ (ENNReal.ofReal r) ^ (s : ℝ))
    (hcover : ∀ᵐ x ∂μ, ∃ n, x ∈ E n) :
    (s : ℝ≥0∞) ≤ lowerHausdorffDimension μ := by
  apply le_iInf
  intro A
  apply le_iInf
  intro _hA
  apply le_iInf
  intro hApos
  apply le_of_not_gt
  intro hdim
  have hHzero := hausdorffMeasure_of_dimH_lt hdim
  have hzero : ∀ n, μ (A ∩ E n) = 0 := by
    intro n
    exact le_antisymm ((restricted_mass_le_hausdorff_of_ball_bound μ (E n) s
      (hε n) (hball n) A).trans_eq hHzero) bot_le
  have hall : ∀ᵐ x ∂μ, ∀ n, x ∉ A ∩ E n := by
    apply ae_all_iff.mpr
    intro n
    change (A ∩ E n)ᶜ ∈ ae μ
    rw [mem_ae_iff, compl_compl]
    exact hzero n
  have hnot : ∀ᵐ x ∂μ, x ∉ A := by
    filter_upwards [hcover, hall] with x hx hnx
    obtain ⟨n, hn⟩ := hx
    exact fun hA ↦ hnx n ⟨hA, hn⟩
  have hz : μ A = 0 := by
    change Aᶜ ∈ ae μ at hnot
    rwa [mem_ae_iff, compl_compl] at hnot
  exact hApos.ne' hz

end ExactOverlaps
