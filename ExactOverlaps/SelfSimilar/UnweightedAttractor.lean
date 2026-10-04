module

public import ExactOverlaps.SelfSimilar.UnweightedSystem
public import ExactOverlaps.SelfSimilar.AttractorUniqueness
public import ExactOverlaps.SelfSimilar.SimilarityDimension

/-!
Existence and uniqueness statements for unweighted finite similarity
families. The auxiliary uniform weights do not change any affine map.
-/

@[expose] public section

open Set

namespace ExactOverlaps.SelfSimilar

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem exists_unique_compact_attractor (g : ι → RealSimilarity)
    (hg : ∀ i, |(g i).ratio| < 1) :
    ∃! K : Set ℝ, IsCompact K ∧ K.Nonempty ∧ K = ⋃ i, (g i) '' K := by
  let S := uniformSystem g hg
  refine ⟨S.attractor, ⟨S.attractor_isCompact, S.attractor_nonempty, S.attractor_eq_union⟩, ?_⟩
  intro K hK
  exact S.eq_attractor_of_compact_invariant hK.1 hK.2.1 hK.2.2

theorem exists_unique_moran_root (g : ι → RealSimilarity)
    (hg : ∀ i, |(g i).ratio| < 1) :
    ∃! s : ℝ, 0 ≤ s ∧ (∑ i, |(g i).ratio| ^ s) = 1 :=
  (uniformSystem g hg).exists_unique_similarity_dimension

end ExactOverlaps.SelfSimilar
