module

public import ExactOverlaps.Probability.CutBlocks
import Lean.Elab.Tactic.Omega

/-!
# Exact cut patterns selecting an index block

A nonempty block is a cell precisely when its internal gaps are uncut and
the neighboring gaps, when they exist, are cut. Boundary conditions are
expressed without introducing fictitious gaps beyond the finite support.
-/

@[expose] public section

open scoped Classical

namespace ExactOverlaps.Poisson

lemma separatingCuts_indexSide_of_le {n : ℕ} (a b : Fin (n + 1)) (hab : a ≤ b) :
    separatingCuts (indexSide n) a b =
      Finset.univ.filter (fun k : Fin n ↦ a.val ≤ k.val ∧ k.val < b.val) := by
  ext k
  simp only [separatingCuts, Finset.mem_filter, Finset.mem_univ, true_and]
  have hab' : a.val ≤ b.val := hab
  by_cases hka : k.val < a.val <;> by_cases hkb : k.val < b.val <;>
    simp [indexSide, hka, hkb] <;> omega

lemma cutLabel_adjacent_iff {n : ℕ} (c : Fin n → Bool) (k : Fin n) :
    cutLabel (indexSide n) c k.castSucc = cutLabel (indexSide n) c k.succ ↔ c k = false := by
  have hs : separatingCuts (indexSide n) k.castSucc k.succ = {k} := by
    rw [separatingCuts_indexSide_of_le _ _ (by change k.val ≤ k.val + 1; omega)]
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    change (k.val ≤ i.val ∧ i.val < k.val + 1) ↔ i = k
    constructor
    · intro h
      exact Fin.ext (by omega)
    · intro h
      subst i
      omega
  rw [cutLabel_eq_iff_no_separating_cut, hs]
  simp

/-- Internal gaps are uncut, and the immediate neighboring gaps are cut when present. -/
def blockPattern {n : ℕ} (c : Fin n → Bool) (a b : Fin (n + 1)) : Prop :=
  a ≤ b ∧ (∀ k : Fin n, a.val ≤ k.val → k.val < b.val → c k = false) ∧
    (∀ k : Fin n, k.val + 1 = a.val → c k = true) ∧
    (∀ k : Fin n, k.val = b.val → c k = true)

lemma indexCell_eq_Icc_of_blockPattern {n : ℕ} (c : Fin n → Bool)
    (a b : Fin (n + 1)) (h : blockPattern c a b) : indexCell c a = Finset.Icc a b := by
  obtain ⟨hab, hint, hleft, hright⟩ := h
  have hab' : a.val ≤ b.val := hab
  have heq : cutLabel (indexSide n) c a = cutLabel (indexSide n) c b := by
    rw [cutLabel_eq_iff_no_separating_cut, separatingCuts_indexSide_of_le a b hab]
    intro k hk
    obtain ⟨_, hak, hkb⟩ := Finset.mem_filter.mp hk
    exact hint k hak hkb
  ext z
  rw [mem_indexCell, Finset.mem_Icc]
  constructor
  · intro hz
    constructor
    · by_contra haz
      have hza : z.val < a.val := by simpa using lt_of_not_ge haz
      let k : Fin n := ⟨a.val - 1, by have ha := a.isLt; omega⟩
      have hk : k.val + 1 = a.val := by dsimp [k]; omega
      have hcut := hleft k hk
      have hside := (cutLabel_eq_iff _ _ _ _).mp hz k hcut
      have hka : k.val < a.val := by omega
      have hkz : ¬ k.val < z.val := by omega
      simp [indexSide, hka, hkz] at hside
    · by_contra hzb
      have hbz : b.val < z.val := by simpa using lt_of_not_ge hzb
      let k : Fin n := ⟨b.val, by have hz := z.isLt; omega⟩
      have hcut := hright k rfl
      have hside := (cutLabel_eq_iff _ _ _ _).mp hz k hcut
      have hkz : k.val < z.val := hbz
      have hka : ¬ k.val < a.val := by dsimp [k]; omega
      simp [indexSide, hkz, hka] at hside
  · rintro ⟨haz, hzb⟩
    exact (cutLabel_between c heq haz hzb).symm

lemma blockPattern_of_indexCell_eq_Icc {n : ℕ} (c : Fin n → Bool)
    (a b : Fin (n + 1)) (h : indexCell c a = Finset.Icc a b) : blockPattern c a b := by
  have ha : a ∈ Finset.Icc a b := by rw [← h]; simp
  have hab := (Finset.mem_Icc.mp ha).2
  have hb : b ∈ indexCell c a := by rw [h]; exact Finset.mem_Icc.mpr ⟨hab, le_rfl⟩
  have heq := ((mem_indexCell c a b).mp hb).symm
  refine ⟨hab, ?_, ?_, ?_⟩
  · intro k hak hkb
    cases hk : c k
    · rfl
    · have hside := (cutLabel_eq_iff _ _ _ _).mp heq k hk
      have hka : ¬ k.val < a.val := by omega
      simp [indexSide, hka, hkb] at hside
  · intro k hka
    cases hk : c k
    · have hlabel := (cutLabel_adjacent_iff c k).mpr hk
      have he : k.succ = a := Fin.ext hka
      rw [he] at hlabel
      have hm := (mem_indexCell c a k.castSucc).mpr hlabel
      rw [h] at hm
      have hbad : a.val ≤ k.val := (Finset.mem_Icc.mp hm).1
      omega
    · rfl
  · intro k hkb
    cases hk : c k
    · have hlabel := (cutLabel_adjacent_iff c k).mpr hk
      have he : k.castSucc = b := Fin.ext hkb
      rw [he] at hlabel
      have hm := (mem_indexCell c a k.succ).mpr (hlabel.symm.trans heq.symm)
      rw [h] at hm
      have hbad : k.val + 1 ≤ b.val := (Finset.mem_Icc.mp hm).2
      omega
    · rfl

lemma indexCell_eq_Icc_iff {n : ℕ} (c : Fin n → Bool) (a b : Fin (n + 1)) :
    indexCell c a = Finset.Icc a b ↔ blockPattern c a b :=
  ⟨blockPattern_of_indexCell_eq_Icc c a b, indexCell_eq_Icc_of_blockPattern c a b⟩

end ExactOverlaps.Poisson
