module

public import ExactOverlaps.SelfSimilar.Dimension
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
Positive lower Hausdorff dimension excludes atoms. A compactly carried
atomless measure assigns uniformly small mass to sufficiently short
intervals, irrespective of the position of the interval. The compactness
argument uses open neighborhoods of null singletons and a Lebesgue number.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped ENNReal

namespace ExactOverlaps

theorem nullSingletonClass_of_lowerHausdorffDimension_pos (μ : Measure ℝ)
    (hμ : 0 < lowerHausdorffDimension μ) : NullSingletonClass μ := by
  constructor
  intro x
  by_contra hx
  have h := lowerHausdorffDimension_le_dimH μ (measurableSet_singleton x)
    (pos_iff_ne_zero.mpr hx)
  have : lowerHausdorffDimension μ ≤ 0 := by simpa using h
  exact (not_lt_of_ge this) hμ

theorem exists_uniform_closedBall_measure_lt (μ : Measure ℝ)
    [IsFiniteMeasure μ] [NullSingletonClass μ]
    {K : Set ℝ} (hK : IsCompact K) (hfull : μ Kᶜ = 0)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, μ (closedBall x δ) < ε := by
  classical
  have hopen (x : ℝ) : ∃ U : Set ℝ, {x} ⊆ U ∧ IsOpen U ∧ μ U < ε :=
    ({x} : Set ℝ).exists_isOpen_lt_of_lt ε (by simpa using hε)
  choose U hxU hUopen hUmass using hopen
  have hcover : K ⊆ ⋃ x : ℝ, U x := by
    intro x _
    exact mem_iUnion.mpr ⟨x, hxU x (mem_singleton x)⟩
  obtain ⟨r, hr, hsub⟩ := lebesgue_number_lemma_of_metric hK hUopen hcover
  refine ⟨r / 3, by positivity, fun x ↦ ?_⟩
  by_cases hne : (closedBall x (r / 3) ∩ K).Nonempty
  · obtain ⟨z, hzball, hzK⟩ := hne
    obtain ⟨y, hy⟩ := hsub z hzK
    have hball : closedBall x (r / 3) ⊆ U y := by
      intro w hw
      apply hy
      apply mem_ball.mpr
      have hdist := dist_triangle w x z
      have hw' := mem_closedBall.mp hw
      have hz' := mem_closedBall.mp hzball
      rw [dist_comm z x] at hz'
      linarith
    exact (measure_mono hball).trans_lt (hUmass y)
  · have hz : μ (closedBall x (r / 3)) = 0 := by
      apply measure_mono_null (t := Kᶜ) _ hfull
      intro z hz hzK
      exact hne ⟨z, hz, hzK⟩
    simpa only [hz] using hε

theorem exists_uniform_interval_measure_lt (μ : Measure ℝ)
    [IsFiniteMeasure μ] [NullSingletonClass μ]
    {K : Set ℝ} (hK : IsCompact K) (hfull : μ Kᶜ = 0)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a b : ℝ, b - a ≤ δ → μ (Icc a b) < ε := by
  obtain ⟨δ, hδ, hball⟩ := exists_uniform_closedBall_measure_lt μ hK hfull hε
  refine ⟨δ, hδ, fun a b hab ↦ ?_⟩
  apply (measure_mono (show Icc a b ⊆ closedBall a δ from ?_)).trans_lt (hball a)
  intro x hx
  rw [mem_closedBall, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hx.1)]
  linarith [hx.2]

end ExactOverlaps
