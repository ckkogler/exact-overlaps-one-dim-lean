module

public import ExactOverlaps.SelfSimilar.BranchInformation
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace

/-!
Differentiation of conditional branch probabilities through shrinking
closed balls. The positive-density almost-sure statement is taken with
respect to the branch measure, exactly where logarithms are needed.
-/

@[expose] public section

open MeasureTheory Filter Metric
open scoped Topology ENNReal

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι]

noncomputable def branchBallInformation (S : System ι) (ν : Measure ℝ)
    (i : ι) (r x : ℝ) : ℝ :=
  -Real.log ((S.branchMeasure ν i (closedBall x r) / ν (closedBall x r)).toReal)

theorem ae_branchDensity_pos (S : System ι) {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : S.IsStationary ν) (i : ι) :
    ∀ᵐ x ∂S.branchMeasure ν i, 0 < S.branchDensity ν i x :=
  Measure.rnDeriv_pos (S.branchMeasure_absolutelyContinuous hν i)

theorem ae_branchBallRatio_tendsto (S : System ι) (ν : Measure ℝ) [IsFiniteMeasure ν]
    (i : ι) : ∀ᵐ x ∂ν, Tendsto
      (fun r : ℝ ↦ S.branchMeasure ν i (closedBall x r) / ν (closedBall x r))
      (𝓝[>] 0) (𝓝 (S.branchDensity ν i x)) :=
  Besicovitch.ae_tendsto_rnDeriv (S.branchMeasure ν i) ν

theorem ae_branchBallInformation_tendsto (S : System ι) {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : S.IsStationary ν) (i : ι) :
    ∀ᵐ x ∂S.branchMeasure ν i, Tendsto (fun r : ℝ ↦ S.branchBallInformation ν i r x)
      (𝓝[>] 0) (𝓝 (S.branchInformation ν i x)) := by
  have hac := S.branchMeasure_absolutelyContinuous hν i
  filter_upwards [hac.ae_le (S.ae_branchBallRatio_tendsto ν i),
    S.ae_branchDensity_pos hν i, hac.ae_le (S.branchDensity_lt_top hν i)] with x hx hpos hfin
  have hr := (ENNReal.continuousAt_toReal hfin.ne).tendsto.comp hx
  have hp : (S.branchDensity ν i x).toReal ≠ 0 :=
    (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'
  simpa only [Function.comp_def, branchBallInformation, branchInformation] using (hr.log hp).neg

end ExactOverlaps.SelfSimilar.System
