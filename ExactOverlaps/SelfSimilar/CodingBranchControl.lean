module

public import ExactOverlaps.SelfSimilar.CodingBranchLaw
public import ExactOverlaps.SelfSimilar.BranchBalls
public import ExactOverlaps.SelfSimilar.BallInformationEnvelope

/-!
Transfer of almost-everywhere branch statements to the actual coding
process, including differentiation and a uniform integrable information
envelope. No positivity assumption on every alphabet weight is needed.
-/

@[expose] public section

open MeasureTheory Filter Metric
open scoped Topology

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem ae_coding_branch_property (S : System ι) (P : ι → ℝ → Prop)
    (hP : ∀ i, ∀ᵐ x ∂S.branchMeasure S.codingMeasure i, P i x) :
    ∀ᵐ ω ∂Bernoulli.sequenceLaw S.alphabetLaw.toMeasure, P (ω 0) (S.coding ω) := by
  have h : ∀ᵐ z ∂(Bernoulli.sequenceLaw S.alphabetLaw.toMeasure).map
      (fun ω ↦ (ω 0, S.coding ω)), P z.1 z.2 := by
    rw [coding_branch_map, ae_finsetSum_measure_iff]
    intro i _
    exact (measurableEmbedding_prodMk_left i).ae_map_iff.mpr (hP i)
  exact ae_of_ae_map ((measurable_pi_apply 0).prodMk S.measurable_coding).aemeasurable h

theorem ae_coding_branchBallInformation_tendsto (S : System ι) :
    ∀ᵐ ω ∂Bernoulli.sequenceLaw S.alphabetLaw.toMeasure,
      Tendsto (fun r : ℝ ↦ S.branchBallInformation S.codingMeasure (ω 0) r (S.coding ω))
        (𝓝[>] 0) (𝓝 (S.branchInformation S.codingMeasure (ω 0) (S.coding ω))) :=
  S.ae_coding_branch_property _ (S.ae_branchBallInformation_tendsto S.codingMeasure_isStationary)

theorem exists_integrable_coding_branchBallInformation_envelope (S : System ι) (R : ℝ) :
    ∃ G : (ℕ → ι) → ℝ, Measurable G ∧
      Integrable G (Bernoulli.sequenceLaw S.alphabetLaw.toMeasure) ∧ (∀ ω, 0 ≤ G ω) ∧
      ∀ᵐ ω ∂Bernoulli.sequenceLaw S.alphabetLaw.toMeasure,
        ∀ r : ℝ, 0 < r → r ≤ R →
          |S.branchBallInformation S.codingMeasure (ω 0) r (S.coding ω)| ≤ G ω := by
  have hex := fun i ↦ exists_integrable_ballInformation_envelope
    (S.branchMeasure S.codingMeasure i) S.codingMeasure
    (S.branchMeasure_le S.codingMeasure_isStationary i) R
  choose G hm hi h0 hbound using hex
  refine ⟨fun ω ↦ G (ω 0) (S.coding ω), ?_,
    S.integrable_coding_branch_observable G hm hi, fun ω ↦ h0 _ _, ?_⟩
  · have hm' : Measurable (fun z : ι × ℝ ↦ G z.1 z.2) :=
      measurable_from_prod_countable_right hm
    exact hm'.comp ((measurable_pi_apply 0).prodMk S.measurable_coding)
  · apply S.ae_coding_branch_property
      (fun i x ↦ ∀ r : ℝ, 0 < r → r ≤ R →
        |S.branchBallInformation S.codingMeasure i r x| ≤ G i x)
    intro i
    simpa only [branchBallInformation, abs_neg] using hbound i

theorem ae_coding_branch_closedBall_pos (S : System ι) :
    ∀ᵐ ω ∂Bernoulli.sequenceLaw S.alphabetLaw.toMeasure, ∀ r : ℝ, 0 < r →
      0 < S.branchMeasure S.codingMeasure (ω 0) (closedBall (S.coding ω) r) :=
  S.ae_coding_branch_property _ (fun _i ↦ ae_closedBall_measure_pos _)

end ExactOverlaps.SelfSimilar.System
