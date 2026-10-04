/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.WFullDimension.NearMaximalEntropy
public import ExactOverlaps.WFullDimension.EntropyDimension

/-!
Vanishing W gives maximal dyadic mesh increments. The fixed positive
factor in the entropy threshold preserves convergence of the physical
mesh to zero. The resulting entropy rate is the standard dimension rate.
-/

@[expose] public section

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace ExactOverlaps.WFullDimension

open ConvolutionDisintegration Entropy ScaleEntropy

theorem entropy_increments_tendsto_of_W_tendsto (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (hW : Tendsto (W μ) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun n : ℕ ↦
      entropy μ hμ ((1 / 2 : ℝ) ^ (n + 1)) (pow_pos (by norm_num) (n + 1)) -
      entropy μ hμ ((1 / 2 : ℝ) ^ n) (pow_pos (by norm_num) n))
      atTop (𝓝 (Real.log 2)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, b, hb, hbound⟩ := exists_W_threshold_for_entropy hε
  have hmesh : Tendsto (fun n : ℕ ↦ δ * (1 / 2 : ℝ) ^ (n + 1))
      atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).comp (tendsto_add_atTop_nat 1)
      simpa only [Function.comp_def, mul_zero] using hp.const_mul δ
    · exact Filter.Eventually.of_forall (fun n ↦ mul_pos hδ (pow_pos (by norm_num) (n + 1)))
  have hsmall : ∀ᶠ n : ℕ in atTop, W μ (δ * (1 / 2 : ℝ) ^ (n + 1)) < b :=
    (hW.comp hmesh).eventually (gt_mem_nhds hb)
  filter_upwards [hsmall] with n hn
  have hr : 0 < (1 / 2 : ℝ) ^ (n + 1) := pow_pos (by norm_num) _
  have hd : (2 : ℝ) * (1 / 2 : ℝ) ^ (n + 1) = (1 / 2 : ℝ) ^ n := by
    rw [pow_succ]
    ring
  have hl := hbound μ hμ _ hr hn
  have hu := (entropyBetween_double_bounds μ hμ _ hr).2
  simp only [entropyBetween, hd] at hl hu
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

theorem dimension_eq_one_of_W_tendsto {ι : Type*} [Fintype ι]
    (S : SelfSimilar.System ι) (μ : ProbabilityMeasure ℝ)
    (hμ : S.IsStationary (μ : Measure ℝ))
    (hW : Tendsto (W μ) (𝓝[>] 0) (𝓝 0)) :
    lowerHausdorffDimension (μ : Measure ℝ) = 1 :=
  dimension_eq_one_of_entropy_increments S μ hμ
    (entropy_increments_tendsto_of_W_tendsto μ (S.hasBoundedSupport hμ) hW)

end ExactOverlaps.WFullDimension
