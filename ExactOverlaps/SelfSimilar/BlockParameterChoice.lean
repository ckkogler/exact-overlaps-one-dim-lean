module

public import ExactOverlaps.SelfSimilar.WordBlockEnergy
public import ExactOverlaps.SelfSimilar.EntropyBridge

/-! Block length and copy number are chosen before the exponential observation scale. -/

@[expose] public section

open Filter
open scoped Topology

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι]

theorem exists_small_blockEntropyPenalty (S : System ι) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, 0 < N ∧ ∃ m : ℕ, 0 < m ∧ S.blockEntropyPenalty N m / N < δ := by
  have hNlim : Tendsto (fun N : ℕ ↦ (Fintype.card ι : ℝ) * Real.log (N + 1 : ℝ) / N)
      atTop (𝓝 0) := by
    simpa only [mul_div_assoc, mul_zero] using
      tendsto_log_nat_add_one_div.const_mul (Fintype.card ι : ℝ)
  obtain ⟨N, hN, hNsmall⟩ := ((eventually_gt_atTop 0).and
    (hNlim.eventually (gt_mem_nhds (half_pos hδ)))).exists
  have hNreal : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  let K : ℝ := (Fintype.card (BoundedWord ι N) - 1 : ℕ)
  have hmlim : Tendsto (fun m : ℕ ↦ K * Real.log (m + 1 : ℝ) / m) atTop (𝓝 0) := by
    simpa only [mul_div_assoc, mul_zero] using tendsto_log_nat_add_one_div.const_mul K
  obtain ⟨m, hm, hmsmall⟩ := ((eventually_gt_atTop 0).and
    (hmlim.eventually (gt_mem_nhds (mul_pos (half_pos hδ) hNreal)))).exists
  refine ⟨N, hN, m, hm, ?_⟩
  apply (div_lt_iff₀ hNreal).mpr
  have hNsmall' := (div_lt_iff₀ hNreal).mp hNsmall
  dsimp [blockEntropyPenalty, K] at hmsmall ⊢
  linarith

end ExactOverlaps.SelfSimilar.System
