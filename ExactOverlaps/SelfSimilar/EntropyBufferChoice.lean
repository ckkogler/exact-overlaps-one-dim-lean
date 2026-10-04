module

public import ExactOverlaps.SelfSimilar.RatioLevelWindows

/-! Quantitative parameter selection for the final vanishing-entropy argument. -/

@[expose] public section

open Filter
open scoped Topology

namespace ExactOverlaps.SelfSimilar

noncomputable def bufferedEntropyLimit (d κ e γ ε q : ℝ) : ℝ :=
  e * ((q - 1) * κ + 2 * ε) * Real.log 2 +
    (2 * d * ε * Real.log 2) / γ + 3 * ε * Real.log 2

theorem exists_positive_entropy_threshold {κ q τ : ℝ} (hτ : 0 < τ) :
    ∃ e : ℝ, 0 < e ∧ e * ((q - 1) * κ) * Real.log 2 < τ / 2 := by
  have hc : Continuous (fun e : ℝ ↦ e * ((q - 1) * κ) * Real.log 2) := by fun_prop
  have hevent : ∀ᶠ e : ℝ in 𝓝 0, e * ((q - 1) * κ) * Real.log 2 < τ / 2 := by
    have h : Tendsto (fun e : ℝ ↦ e * ((q - 1) * κ) * Real.log 2) (𝓝 0) (𝓝 0) := by
      simpa only [zero_mul] using hc.tendsto 0
    exact h.eventually (gt_mem_nhds (half_pos hτ))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨δ / 2, half_pos hδ, hball ?_⟩
  simpa only [Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)] using (half_lt_self hδ)

theorem exists_positive_entropy_buffer {d κ e γ q τ : ℝ}
    (hκ : 0 < κ) (hq : 1 < q)
    (hbase : e * ((q - 1) * κ) * Real.log 2 < τ) :
    ∃ ε : ℝ, 0 < ε ∧ 2 * ε < κ ∧ 0 < (q - 1) * κ - ε ∧
      bufferedEntropyLimit d κ e γ ε q < τ := by
  have hc : Continuous (fun ε : ℝ ↦ bufferedEntropyLimit d κ e γ ε q) := by
    unfold bufferedEntropyLimit
    fun_prop
  have hB : ∀ᶠ ε : ℝ in 𝓝 0, bufferedEntropyLimit d κ e γ ε q < τ := by
    have h : Tendsto (fun ε : ℝ ↦ bufferedEntropyLimit d κ e γ ε q) (𝓝 0)
        (𝓝 (e * ((q - 1) * κ) * Real.log 2)) := by
      simpa only [bufferedEntropyLimit, mul_zero, zero_mul, zero_div, add_zero] using hc.tendsto 0
    exact h.eventually (gt_mem_nhds hbase)
  have hκevent : ∀ᶠ ε : ℝ in 𝓝 0, ε < κ / 2 := eventually_lt_nhds (half_pos hκ)
  have hqevent : ∀ᶠ ε : ℝ in 𝓝 0, ε < (q - 1) * κ :=
    eventually_lt_nhds (mul_pos (sub_pos.mpr hq) hκ)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (hκevent.and (hqevent.and hB))
  have hh := hball (y := δ / 2) (by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)] using (half_lt_self hδ))
  exact ⟨δ / 2, half_pos hδ, by linarith [hh.1], sub_pos.mpr hh.2.1, hh.2.2⟩

end ExactOverlaps.SelfSimilar
