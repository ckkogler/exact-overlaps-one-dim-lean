module

public import ExactOverlaps.SelfSimilar.Definitions
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.Order.IntermediateValue

/-!
The similarity dimension is the unique nonnegative solution of the Moran
equation. The existence proof includes a one-branch system, whose solution
is zero, and keeps the absolute values of signed contraction ratios.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι]

noncomputable def pressure (S : System ι) (s : ℝ) : ℝ :=
  ∑ i, |(S.map i).ratio| ^ s

theorem pressure_continuous (S : System ι) : Continuous S.pressure :=
  continuous_finsetSum _ (fun i _ ↦ Real.continuous_const_rpow (S.map i).abs_ratio_pos.ne')

theorem pressure_strictAnti (S : System ι) : StrictAnti S.pressure := by
  intro a b hab
  apply Finset.sum_lt_sum
  · intro i _
    exact (Real.rpow_lt_rpow_of_exponent_gt (S.map i).abs_ratio_pos (S.contracting i) hab).le
  · obtain ⟨i⟩ := S.nonempty_index
    exact ⟨i, Finset.mem_univ _,
      Real.rpow_lt_rpow_of_exponent_gt (S.map i).abs_ratio_pos (S.contracting i) hab⟩

theorem pressure_zero (S : System ι) : S.pressure 0 = Fintype.card ι := by
  simp [pressure]

theorem pressure_tendsto_zero (S : System ι) :
    Tendsto S.pressure atTop (𝓝 0) := by
  change Tendsto (fun s : ℝ ↦ ∑ i, |(S.map i).ratio| ^ s) atTop (𝓝 0)
  have h := tendsto_finsetSum Finset.univ (fun i _ ↦
    tendsto_rpow_atTop_of_base_lt_one |(S.map i).ratio|
      (by linarith [(S.map i).abs_ratio_pos]) (S.contracting i))
  simpa only [Finset.sum_const_zero] using h

theorem exists_unique_similarity_dimension (S : System ι) :
    ∃! s : ℝ, 0 ≤ s ∧ S.pressure s = 1 := by
  have hsmall := S.pressure_tendsto_zero.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨b, hb0, hb⟩ := ((eventually_ge_atTop (0 : ℝ)).and hsmall).exists
  have hzero : 1 ≤ S.pressure 0 := by
    rw [S.pressure_zero]
    have := S.nonempty_index
    exact_mod_cast Fintype.card_pos_iff.mpr this
  obtain ⟨s, hs, he⟩ := intermediate_value_Icc' hb0 S.pressure_continuous.continuousOn ⟨hb.le, hzero⟩
  refine ⟨s, ⟨hs.1, he⟩, ?_⟩
  intro t ht
  exact S.pressure_strictAnti.injective (ht.2.trans he.symm)

noncomputable def similarityDimension (S : System ι) : ℝ :=
  S.exists_unique_similarity_dimension.choose

theorem similarityDimension_nonneg (S : System ι) : 0 ≤ S.similarityDimension :=
  S.exists_unique_similarity_dimension.choose_spec.1.1

theorem pressure_similarityDimension (S : System ι) :
    S.pressure S.similarityDimension = 1 :=
  S.exists_unique_similarity_dimension.choose_spec.1.2

theorem similarityDimension_unique (S : System ι) {s : ℝ} (hs : S.pressure s = 1) :
    s = S.similarityDimension :=
  S.pressure_strictAnti.injective (hs.trans S.pressure_similarityDimension.symm)

end ExactOverlaps.SelfSimilar.System
