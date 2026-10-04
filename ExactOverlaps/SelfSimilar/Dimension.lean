module

public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
Standard measure dimensions used in the self-similar statements. Lower
Hausdorff dimension is defined through positive-measure Borel sets. Exact
dimension is defined by the almost-everywhere limit of logarithmic ball
masses. Their equivalence for exact-dimensional measures is a proof
obligation, not part of either definition.
-/

@[expose] public section

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

namespace ExactOverlaps

/-- Lower Hausdorff dimension of a real Borel measure. -/
noncomputable def lowerHausdorffDimension (μ : Measure ℝ) : ℝ≥0∞ :=
  ⨅ E : Set ℝ, ⨅ (_ : MeasurableSet E) (_ : 0 < μ E), dimH E

/-- The standard local dimension limit, with closed balls and natural logs. -/
def HasExactDimension (μ : Measure ℝ) (α : ℝ) : Prop :=
  ∀ᵐ x ∂μ, Tendsto
    (fun r : ℝ ↦ Real.log (μ (closedBall x r)).toReal / Real.log r)
    (𝓝[>] (0 : ℝ)) (𝓝 α)

theorem lowerHausdorffDimension_le_dimH (μ : Measure ℝ) {E : Set ℝ}
    (hE : MeasurableSet E) (hpos : 0 < μ E) : lowerHausdorffDimension μ ≤ dimH E :=
  iInf_le_of_le E (iInf_le_of_le hE (iInf_le _ hpos))

theorem lowerHausdorffDimension_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    lowerHausdorffDimension μ ≤ 1 := by
  have h := lowerHausdorffDimension_le_dimH μ MeasurableSet.univ
    (show 0 < μ Set.univ by simp)
  simpa only [Real.dimH_univ] using h

theorem lowerHausdorffDimension_ne_top (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    lowerHausdorffDimension μ ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (lowerHausdorffDimension_le_one μ)

/-- A probability measure has at most one almost-sure exact dimension. -/
theorem HasExactDimension.unique {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {α β : ℝ} (hα : HasExactDimension μ α) (hβ : HasExactDimension μ β) : α = β := by
  obtain ⟨x, hx, hx'⟩ := (hα.and hβ).exists
  exact tendsto_nhds_unique hx hx'

end ExactOverlaps
