module

public import ExactOverlaps.Probability.CutBlockPatterns

/-!
# Labeling each cut cell by its endpoints

The endpoint pair is an equivalent observation label. Its fiber at `(a,b)`
is the interval `[a,b]` exactly when the neighboring-cut pattern makes that
interval a cell; all other endpoint fibers are empty.
-/

@[expose] public section

open scoped Classical

namespace ExactOverlaps.Poisson

noncomputable def cellEndpoints {n : ℕ} (c : Fin n → Bool) (a : Fin (n + 1)) :
    Fin (n + 1) × Fin (n + 1) := (cellFirst c a, cellLast c a)

lemma cellEndpoints_eq_iff {n : ℕ} (c : Fin n → Bool) (a b : Fin (n + 1)) :
    cellEndpoints c a = cellEndpoints c b ↔
      cutLabel (indexSide n) c a = cutLabel (indexSide n) c b := by
  constructor
  · intro h
    have hf : cellFirst c a = cellFirst c b := congrArg Prod.fst h
    have hl : cellLast c a = cellLast c b := congrArg Prod.snd h
    have he : indexCell c a = indexCell c b := by
      rw [indexCell_eq_Icc c a, indexCell_eq_Icc c b, hf, hl]
    have ha : a ∈ indexCell c b := by rw [← he]; simp
    exact (mem_indexCell c b a).mp ha
  · intro h
    exact Prod.ext (cellFirst_eq_of_label_eq c h) (cellLast_eq_of_label_eq c h)

lemma cellFirst_eq_of_blockPattern {n : ℕ} (c : Fin n → Bool)
    (a b : Fin (n + 1)) (h : blockPattern c a b) : cellFirst c a = a := by
  apply le_antisymm (cellFirst_le c a)
  have hm := cellFirst_mem c a
  rw [indexCell_eq_Icc_of_blockPattern c a b h] at hm
  exact (Finset.mem_Icc.mp hm).1

lemma cellLast_eq_of_blockPattern {n : ℕ} (c : Fin n → Bool)
    (a b : Fin (n + 1)) (h : blockPattern c a b) : cellLast c a = b := by
  have hm := cellLast_mem c a
  rw [indexCell_eq_Icc_of_blockPattern c a b h] at hm
  apply le_antisymm (Finset.mem_Icc.mp hm).2
  have hb : b ∈ indexCell c a := by
    rw [indexCell_eq_Icc_of_blockPattern c a b h]
    exact Finset.mem_Icc.mpr ⟨h.1, le_rfl⟩
  exact Finset.le_max' _ _ hb

/-- Exact description of every endpoint-label fiber, with no positivity assumptions on atoms. -/
lemma cellEndpoints_eq_pair_iff {n : ℕ} (c : Fin n → Bool)
    (z a b : Fin (n + 1)) :
    cellEndpoints c z = (a, b) ↔ blockPattern c a b ∧ z ∈ Finset.Icc a b := by
  constructor
  · intro h
    have hf : cellFirst c z = a := congrArg Prod.fst h
    have hl : cellLast c z = b := congrArg Prod.snd h
    have hz : indexCell c z = Finset.Icc a b := by rw [indexCell_eq_Icc c z, hf, hl]
    have ha : a ∈ indexCell c z := by rw [← hf]; exact cellFirst_mem c z
    have halabel := (mem_indexCell c z a).mp ha
    have he : indexCell c a = Finset.Icc a b :=
      (indexCell_eq_of_label_eq c halabel).trans hz
    refine ⟨blockPattern_of_indexCell_eq_Icc c a b he, ?_⟩
    rw [← hz]
    simp
  · rintro ⟨h, hz⟩
    have hmem : z ∈ indexCell c a := by rw [indexCell_eq_Icc_of_blockPattern c a b h]; exact hz
    have he := (mem_indexCell c a z).mp hmem
    apply Prod.ext
    · exact (cellFirst_eq_of_label_eq c he).trans (cellFirst_eq_of_blockPattern c a b h)
    · exact (cellLast_eq_of_label_eq c he).trans (cellLast_eq_of_blockPattern c a b h)

end ExactOverlaps.Poisson
