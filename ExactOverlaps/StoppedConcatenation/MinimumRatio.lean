/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.ThresholdTimes

/-! The exact minimum contraction ratio, including listed zero-weight branches. -/

@[expose] public section

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι]

theorem minimumRatioWitness (S : System ι) :
    ∃ i : ι, ∀ j : ι, |(S.map i).ratio| ≤ |(S.map j).ratio| := by
  classical
  have := S.nonempty_index
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ
    (fun i ↦ |(S.map i).ratio|) Finset.univ_nonempty
  exact ⟨i, fun j ↦ hi j (Finset.mem_univ j)⟩

noncomputable def rhoMin (S : System ι) : ℝ := |(S.map S.minimumRatioWitness.choose).ratio|

theorem rhoMin_attained (S : System ι) : ∃ i : ι, S.rhoMin = |(S.map i).ratio| :=
  ⟨S.minimumRatioWitness.choose, rfl⟩

theorem rhoMin_le (S : System ι) (i : ι) : S.rhoMin ≤ |(S.map i).ratio| :=
  S.minimumRatioWitness.choose_spec i

theorem rhoMin_pos (S : System ι) : 0 < S.rhoMin :=
  (S.map S.minimumRatioWitness.choose).abs_ratio_pos

theorem rhoMin_lt_one (S : System ι) : S.rhoMin < 1 :=
  S.contracting S.minimumRatioWitness.choose

theorem ratioCrossingTime_rhoMin_lower (S : System ι) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (ω : ℕ → ι) : S.rhoMin * r < |S.prefixRatio (S.ratioCrossingTime r hr ω) ω| :=
  S.ratioCrossingTime_lower r hr hr1 S.rhoMin_pos S.rhoMin_lt_one S.rhoMin_le ω

end ExactOverlaps.SelfSimilar.System
