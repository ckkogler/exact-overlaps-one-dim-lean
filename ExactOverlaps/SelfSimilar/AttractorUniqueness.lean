module

public import ExactOverlaps.SelfSimilar.Attractor
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
Uniqueness of the nonempty compact invariant set. The Hausdorff distance
between any two such sets contracts by a common factor strictly below one.
-/

@[expose] public section

open Set Metric

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι]

theorem invariant_point_distance (S : System ι) {K L : Set ℝ}
    (hK : IsCompact K) (hKn : K.Nonempty) (hL : IsCompact L) (hLn : L.Nonempty)
    (hKi : K = ⋃ i, (S.map i) '' K) (hLi : L = ⋃ i, (S.map i) '' L)
    {c : ℝ} (hmax : ∀ i, |(S.map i).ratio| ≤ c) (x : ℝ) (hx : x ∈ K) :
    ∃ y ∈ L, dist x y ≤ c * hausdorffDist K L := by
  rw [hKi] at hx
  obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.mp hx
  obtain ⟨w, hw, he⟩ := hL.exists_infDist_eq_dist hLn z
  have hfin := hausdorffEDist_ne_top_of_nonempty_of_bounded hKn hLn hK.isBounded hL.isBounded
  have hd : dist z w ≤ hausdorffDist K L := by
    rw [← he]
    exact infDist_le_hausdorffDist_of_mem hz hfin
  refine ⟨S.map i w, ?_, ?_⟩
  · rw [hLi]
    exact mem_iUnion.mpr ⟨i, ⟨w, hw, rfl⟩⟩
  · rw [(S.map i).dist_eq]
    exact mul_le_mul (hmax i) hd dist_nonneg
      ((S.map i).abs_ratio_pos.le.trans (hmax i))

theorem compact_invariant_unique (S : System ι) {K L : Set ℝ}
    (hK : IsCompact K) (hKn : K.Nonempty) (hL : IsCompact L) (hLn : L.Nonempty)
    (hKi : K = ⋃ i, (S.map i) '' K) (hLi : L = ⋃ i, (S.map i) '' L) : K = L := by
  obtain ⟨c, _, hc, hc1, _, hmax, _⟩ := S.exists_uniform_bounds
  have hD : 0 ≤ hausdorffDist K L := hausdorffDist_nonneg
  have hle : hausdorffDist K L ≤ c * hausdorffDist K L := by
    apply hausdorffDist_le_of_mem_dist (mul_nonneg hc.le hD)
    · exact S.invariant_point_distance hK hKn hL hLn hKi hLi hmax
    · intro y hy
      simpa only [hausdorffDist_comm (s := L) (t := K)] using
        S.invariant_point_distance hL hLn hK hKn hLi hKi hmax y hy
  have hz : hausdorffDist K L = 0 := by nlinarith
  exact (hK.isClosed.hausdorffDist_zero_iff_eq hL.isClosed
    (hausdorffEDist_ne_top_of_nonempty_of_bounded hKn hLn hK.isBounded hL.isBounded)).mp hz

theorem eq_attractor_of_compact_invariant (S : System ι) {K : Set ℝ}
    (hK : IsCompact K) (hKn : K.Nonempty) (hKi : K = ⋃ i, (S.map i) '' K) :
    K = S.attractor :=
  S.compact_invariant_unique hK hKn S.attractor_isCompact S.attractor_nonempty hKi S.attractor_eq_union

end ExactOverlaps.SelfSimilar.System
