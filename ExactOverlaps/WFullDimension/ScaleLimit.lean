/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
A positive-power comparison between scales transfers arbitrarily small
values along a sequence to a limit at every sufficiently small scale.
-/

@[expose] public section

open Filter
open scoped Topology

namespace ExactOverlaps.WFullDimension

theorem tendsto_zero_of_power_scale_bound {F : ℝ → ℝ} {a : ℝ}
    (ha : 0 < a) (hF : ∀ s, 0 < s → 0 ≤ F s)
    (hscale : ∀ s t, 0 < s → s ≤ t → F s ≤ (F t) ^ a)
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n)
    (hseq : Tendsto (fun n ↦ F (r n)) atTop (𝓝 0)) :
    Tendsto F (𝓝[>] 0) (𝓝 0) := by
  have hpow : Tendsto (fun n ↦ (F (r n)) ^ a) atTop (𝓝 0) := by
    simpa only [Real.zero_rpow ha.ne', Function.comp_def] using
      (Real.continuous_rpow_const ha.le).continuousAt.tendsto.comp hseq
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := (hpow.eventually (gt_mem_nhds hε)).exists
  have hs : ∀ᶠ s : ℝ in 𝓝[>] 0, s < r n :=
    (gt_mem_nhds (hr n)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hs, self_mem_nhdsWithin] with s hs hpos
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hF s hpos)]
  exact (hscale s (r n) hpos hs.le).trans_lt hn

end ExactOverlaps.WFullDimension
