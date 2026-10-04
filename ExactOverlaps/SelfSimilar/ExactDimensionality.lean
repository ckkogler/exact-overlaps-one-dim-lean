module

public import ExactOverlaps.SelfSimilar.CodingMassLimit
public import ExactOverlaps.SelfSimilar.ExactDimensionTransfer
public import ExactOverlaps.SelfSimilar.StationaryUniqueness

/-!
Exact dimensionality of every finite contracting real self-similar
probability measure, including signed ratios and zero-weight symbols.
The proof uses the actual Bernoulli coding law, conditional branch
information, triangular averaging, and arbitrary-radius interpolation.
-/

@[expose] public section

open MeasureTheory Filter Metric
open scoped Topology

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι]

theorem prefix_radius_antitone (S : System ι) {r : ℝ} (hr : 0 ≤ r) (ω : ℕ → ι) :
    Antitone (fun n ↦ |S.prefixRatio n ω| * r) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [prefixRatio_succ, abs_mul]
  apply mul_le_mul_of_nonneg_right _ hr
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (S.contracting (ω n)).le
    (abs_nonneg (S.prefixRatio n ω))

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem ae_coding_local_dimension (S : System ι) :
    ∀ᵐ ω ∂Bernoulli.sequenceLaw S.alphabetLaw.toMeasure,
      Tendsto (fun t : ℝ ↦ Real.log (S.codingMeasure (closedBall (S.coding ω) t)).toReal /
        Real.log t) (𝓝[>] 0) (𝓝 (S.codingLogMassRate / S.lyapunov)) := by
  obtain ⟨r, hr, hbase⟩ := S.exists_coding_full_ball_radius
  have hpos : ∀ᵐ ω ∂Bernoulli.sequenceLaw S.alphabetLaw.toMeasure,
      ∀ t : ℝ, 0 < t → 0 < S.codingMeasure (closedBall (S.coding ω) t) :=
    ae_of_ae_map S.measurable_coding.aemeasurable (ae_closedBall_measure_pos S.codingMeasure)
  filter_upwards [hpos, S.ae_log_prefixBallMass_div_tendsto hr hbase,
    S.ae_log_prefix_radius_div_tendsto hr] with ω hp hm hrate
  have hi : Tendsto (fun n : ℕ ↦
      ballInformation S.codingMeasure (S.coding ω) (|S.prefixRatio n ω| * r) / n)
      atTop (𝓝 (-S.codingLogMassRate)) := by
    simpa only [ballInformation, prefixBallMass, neg_div] using hm.neg
  have hl : Tendsto (fun n : ℕ ↦ -Real.log (|S.prefixRatio n ω| * r) / n)
      atTop (𝓝 (-S.lyapunov)) := by
    simpa only [neg_div] using hrate.neg
  have h := local_dimension_of_sampled_information S.codingMeasure (S.coding ω) hp
    (fun n ↦ mul_pos (abs_pos.mpr (S.prefixRatio_ne_zero n ω)) hr)
    (S.prefix_radius_antitone hr.le ω)
    (tendsto_nhdsWithin_iff.mp (S.prefix_radius_tendsto_zero hr ω)).1
    (neg_pos.mpr S.lyapunov_neg) hi hl
  simpa only [neg_div_neg_eq] using h

theorem codingMeasure_hasExactDimension (S : System ι) :
    HasExactDimension S.codingMeasure (S.codingLogMassRate / S.lyapunov) :=
  hasExactDimension_of_map_ae_local_limit
    (Bernoulli.sequenceLaw S.alphabetLaw.toMeasure) S.codingMeasure
    S.measurable_coding rfl S.ae_coding_local_dimension

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Every stationary probability of a finite signed contracting affine system is exact dimensional. -/
theorem exists_exactDimension (S : System ι) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : S.IsStationary ν) : ∃ d : ℝ, HasExactDimension ν d := by
  let : MeasurableSpace ι := ⊤
  have : MeasurableSingletonClass ι := ⟨fun _ ↦ trivial⟩
  rw [S.stationary_eq_codingMeasure ν hν]
  exact ⟨S.codingLogMassRate / S.lyapunov, S.codingMeasure_hasExactDimension⟩

end ExactOverlaps.SelfSimilar.System
