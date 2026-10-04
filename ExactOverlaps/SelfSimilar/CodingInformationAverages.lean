module

public import ExactOverlaps.SelfSimilar.CodingBranchControl
public import ExactOverlaps.SelfSimilar.CodingOrbit
public import ExactOverlaps.SelfSimilar.BernoulliTriangular

/-!
The conditional branch information at actual prefix-contraction radii
has the required triangular average limit. The radii are measurable,
positive, uniformly bounded, and tend to zero at every coding sequence.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem measurable_prefixRatio (S : System ι) (n : ℕ) : Measurable (S.prefixRatio n) := by
  have hr : Measurable (fun i ↦ (S.map i).ratio) := measurable_of_finite _
  exact Finset.measurable_fun_prod _ (fun j _ ↦ hr.comp (measurable_pi_apply j))

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
theorem abs_prefixRatio_le_one (S : System ι) (n : ℕ) (ω : ℕ → ι) :
    |S.prefixRatio n ω| ≤ 1 := by
  simpa only [one_pow] using S.abs_prefixRatio_le (by norm_num : (0 : ℝ) ≤ 1)
    (fun i ↦ (S.contracting i).le) n ω

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
theorem prefix_radius_tendsto_zero (S : System ι) {r : ℝ} (hr : 0 < r) (ω : ℕ → ι) :
    Tendsto (fun n ↦ |S.prefixRatio n ω| * r) atTop (𝓝[>] (0 : ℝ)) := by
  obtain ⟨c, M, hc, hc1, _, hmax, _⟩ := S.exists_uniform_bounds
  have habs : Tendsto (fun n ↦ |S.prefixRatio n ω|) atTop (𝓝 (0 : ℝ)) :=
    squeeze_zero (fun n ↦ abs_nonneg _) (fun n ↦ S.abs_prefixRatio_le hc.le hmax n ω)
      (tendsto_pow_atTop_nhds_zero_of_lt_one hc.le hc1)
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨by simpa only [zero_mul] using habs.mul_const r, ?_⟩
  exact Eventually.of_forall (fun n ↦ mul_pos (abs_pos.mpr (S.prefixRatio_ne_zero n ω)) hr)

noncomputable def prefixBranchInformation (S : System ι) (r : ℝ)
    (n : ℕ) (ω : ℕ → ι) : ℝ :=
  S.branchBallInformation S.codingMeasure (ω 0) (|S.prefixRatio n ω| * r) (S.coding ω)

theorem measurable_prefixBranchInformation (S : System ι) (r : ℝ) (n : ℕ) :
    Measurable (S.prefixBranchInformation r n) := by
  have hrn : Measurable (fun ω ↦ |S.prefixRatio n ω| * r) := by
    simpa only [Real.norm_eq_abs] using (S.measurable_prefixRatio n).norm.mul_const r
  exact S.measurable_branchBallInformation_of_index S.codingMeasure
    (measurable_pi_apply 0) hrn S.measurable_coding

theorem ae_prefixBranchInformation_tendsto (S : System ι) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂Bernoulli.sequenceLaw S.alphabetLaw.toMeasure,
      Tendsto (fun n ↦ S.prefixBranchInformation r n ω) atTop
        (𝓝 (S.branchInformation S.codingMeasure (ω 0) (S.coding ω))) := by
  filter_upwards [S.ae_coding_branchBallInformation_tendsto] with ω hω
  exact hω.comp (S.prefix_radius_tendsto_zero hr ω)

theorem ae_prefixBranchInformation_triangular_average (S : System ι) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂Bernoulli.sequenceLaw S.alphabetLaw.toMeasure,
      Tendsto (fun n ↦ Ergodic.triangularAverage Bernoulli.shift
        (S.prefixBranchInformation r) n ω) atTop
        (𝓝 (∫ v, S.branchInformation S.codingMeasure (v 0) (S.coding v)
          ∂Bernoulli.sequenceLaw S.alphabetLaw.toMeasure)) := by
  obtain ⟨G, hGm, hGi, _, hGb⟩ := S.exists_integrable_coding_branchBallInformation_envelope r
  have hfm : Measurable (fun ω ↦ S.branchInformation S.codingMeasure (ω 0) (S.coding ω)) := by
    have hm : Measurable (fun z : ι × ℝ ↦ S.branchInformation S.codingMeasure z.1 z.2) :=
      measurable_from_prod_countable_right (S.measurable_branchInformation S.codingMeasure)
    exact hm.comp ((measurable_pi_apply 0).prodMk S.measurable_coding)
  apply Bernoulli.ae_tendsto_triangularAverage S.alphabetLaw.toMeasure
    (S.measurable_prefixBranchInformation r) hfm hGm hGi _ (S.ae_prefixBranchInformation_tendsto hr)
  filter_upwards [hGb, S.ae_prefixBranchInformation_tendsto hr] with ω hb hlim
  have hn : ∀ n, |S.prefixBranchInformation r n ω| ≤ G ω := by
    intro n
    exact hb _ (mul_pos (abs_pos.mpr (S.prefixRatio_ne_zero n ω)) hr)
      (by simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right (S.abs_prefixRatio_le_one n ω) hr.le))
  exact ⟨hn, le_of_tendsto_of_tendsto' hlim.abs tendsto_const_nhds hn⟩

end ExactOverlaps.SelfSimilar.System
