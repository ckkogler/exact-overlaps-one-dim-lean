module

public import ExactOverlaps.SelfSimilar.CouplingDistribution
public import ExactOverlaps.SelfSimilar.StationaryApproximation
public import ExactOverlaps.SelfSimilar.CodingLaw

/-!
Uniqueness of the actual stationary probability measure. Two stationary
laws are compared to the same finite-word translation law using genuine
couplings, then the geometric tail displacement is sent to zero. The
unique law is therefore the distribution of the affine coding series.
-/

@[expose] public section

open MeasureTheory Set

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι]

theorem stationary_Iic_le (S : System ι) (ν₁ ν₂ : ProbabilityMeasure ℝ)
    (h₁ : S.IsStationary (ν₁ : Measure ℝ)) (h₂ : S.IsStationary (ν₂ : Measure ℝ))
    (x : ℝ) : (ν₁ : Measure ℝ) (Iic x) ≤ (ν₂ : Measure ℝ) (Iic x) := by
  obtain ⟨c, M, hc, hc1, _, hmax, _⟩ := S.exists_uniform_bounds
  obtain ⟨R₁, hR₁, hfull₁⟩ := S.exists_closedBall_full_measure h₁
  obtain ⟨R₂, hR₂, hfull₂⟩ := S.exists_closedBall_full_measure h₂
  have hb₁ : ∀ᵐ z ∂(ν₁ : Measure ℝ), |z| ≤ R₁ := by
    have h : ∀ᵐ z ∂(ν₁ : Measure ℝ), z ∈ Metric.closedBall (0 : ℝ) R₁ :=
      mem_ae_iff.mpr hfull₁
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using h
  have hb₂ : ∀ᵐ z ∂(ν₂ : Measure ℝ), |z| ≤ R₂ := by
    have h : ∀ᵐ z ∂(ν₂ : Measure ℝ), z ∈ Metric.closedBall (0 : ℝ) R₂ :=
      mem_ae_iff.mpr hfull₂
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using h
  rw [measure_Iic_eq_iInf_geometric (ν₂ : Measure ℝ) hc.le hc1 (add_nonneg hR₁.le hR₂.le) x]
  apply le_iInf
  intro n
  have hleft := coupling_snd_Iic_le_fst (S.wordCoupling ν₁ n)
    (S.wordCoupling_displacement ν₁ hc.le hmax hb₁ n) x
  have hright := coupling_fst_Iic_le_snd (S.wordCoupling ν₂ n)
    (S.wordCoupling_displacement ν₂ hc.le hmax hb₂ n) (x + c ^ n * R₁)
  rw [S.wordCoupling_map_snd ν₁ h₁ n, S.wordCoupling_map_fst_probability ν₁ n] at hleft
  rw [S.wordCoupling_map_snd ν₂ h₂ n, S.wordCoupling_map_fst_probability ν₂ n] at hright
  have heq : x + c ^ n * R₁ + c ^ n * R₂ = x + c ^ n * (R₁ + R₂) := by ring
  rw [heq] at hright
  exact hleft.trans hright

/-- A finite contracting affine system has at most one stationary probability. -/
theorem stationary_probability_unique (S : System ι) (ν₁ ν₂ : ProbabilityMeasure ℝ)
    (h₁ : S.IsStationary (ν₁ : Measure ℝ)) (h₂ : S.IsStationary (ν₂ : Measure ℝ)) :
    ν₁ = ν₂ := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_Iic
  intro x
  exact le_antisymm (S.stationary_Iic_le ν₁ ν₂ h₁ h₂ x)
    (S.stationary_Iic_le ν₂ ν₁ h₂ h₁ x)

theorem stationary_measure_unique (S : System ι) (ν₁ ν₂ : Measure ℝ)
    [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (h₁ : S.IsStationary ν₁) (h₂ : S.IsStationary ν₂) : ν₁ = ν₂ := by
  exact congrArg ProbabilityMeasure.toMeasure
    (S.stationary_probability_unique ν₁.toProbabilityMeasure ν₂.toProbabilityMeasure h₁ h₂)

theorem stationary_eq_codingMeasure [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (S : System ι) (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : S.IsStationary ν) :
    ν = S.codingMeasure :=
  S.stationary_measure_unique ν S.codingMeasure hν S.codingMeasure_isStationary

end ExactOverlaps.SelfSimilar.System
