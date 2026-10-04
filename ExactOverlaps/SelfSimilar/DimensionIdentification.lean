module

public import ExactOverlaps.SelfSimilar.ExactDimensionality
public import ExactOverlaps.SelfSimilar.UpperHausdorffBound
public import ExactOverlaps.SelfSimilar.ExactDimensionEntropy
public import ExactOverlaps.SelfSimilar.EntropyBridge

/-!
The exact, lower Hausdorff, and dyadic entropy dimensions agree for the
actual stationary probability of every finite signed contracting affine
system. Each equality uses the proved standard measure-theoretic limits.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace ExactOverlaps

theorem HasExactDimension.nonneg {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {d : ℝ} (hd : HasExactDimension μ d) : 0 ≤ d := by
  obtain ⟨x, hx⟩ := hd.exists
  have h := local_limit_dyadic_information μ x hx
  have hnonneg : 0 ≤ d * Real.log 2 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds h (fun n ↦
      div_nonneg (ballInformation_nonneg μ x _) (Nat.cast_nonneg n))
  exact nonneg_of_mul_nonneg_left hnonneg (Real.log_pos (by norm_num))

theorem HasExactDimension.lowerHausdorffDimension_toReal {μ : Measure ℝ}
    [IsProbabilityMeasure μ] {d : ℝ} (hd : HasExactDimension μ d) :
    (lowerHausdorffDimension μ).toReal = d := by
  rw [hd.lowerHausdorffDimension_eq, ENNReal.toReal_ofReal hd.nonneg]

namespace SelfSimilar.System

variable {ι : Type*} [Fintype ι]

theorem hasExactDimension_lowerHausdorffDimension (S : System ι) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hν : S.IsStationary ν) :
    HasExactDimension ν (lowerHausdorffDimension ν).toReal := by
  obtain ⟨d, hd⟩ := S.exists_exactDimension ν hν
  rw [hd.lowerHausdorffDimension_toReal]
  exact hd

theorem normalizedDyadicEntropy_tendsto_dimension (S : System ι) (ν : ProbabilityMeasure ℝ)
    (hν : S.IsStationary (ν : Measure ℝ)) :
    Tendsto (Entropy.normalizedDyadicEntropy ν (S.hasBoundedSupport hν)) atTop
      (𝓝 (lowerHausdorffDimension (ν : Measure ℝ)).toReal) :=
  Entropy.normalized_entropy_limit_of_exact_dimension ν (S.hasBoundedSupport hν)
    (S.hasExactDimension_lowerHausdorffDimension ν hν)

end SelfSimilar.System
end ExactOverlaps
