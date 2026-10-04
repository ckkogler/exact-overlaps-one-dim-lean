module

public import ExactOverlaps.Probability.OrderedGapCuts
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Interval.Finset.Fin
import Lean.Elab.Tactic.Omega

/-!
# Contiguous blocks in a finite gap-cut partition

Every fiber of the side-of-cut observation is an interval of atom indices.
Its first and last indices are genuine members of the cell, including
singleton cells and the two boundary cells.
-/

@[expose] public section

open scoped Classical

namespace ExactOverlaps.Poisson

lemma cutLabel_between {n : ℕ} (c : Fin n → Bool) {a b z : Fin (n + 1)}
    (hab : cutLabel (indexSide n) c a = cutLabel (indexSide n) c b)
    (haz : a ≤ z) (hzb : z ≤ b) :
    cutLabel (indexSide n) c a = cutLabel (indexSide n) c z := by
  apply (cutLabel_eq_iff _ _ _ _).mpr
  intro i hi
  have hside := (cutLabel_eq_iff _ _ _ _).mp hab i hi
  have haz' : a.val ≤ z.val := haz
  have hzb' : z.val ≤ b.val := hzb
  by_cases hia : i.val < a.val <;> by_cases hiz : i.val < z.val <;>
    by_cases hib : i.val < b.val <;> simp_all [indexSide] <;> omega

/-- The complete set of atom indices in the observation cell containing `a`. -/
noncomputable def indexCell {n : ℕ} (c : Fin n → Bool) (a : Fin (n + 1)) :
    Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun b ↦ cutLabel (indexSide n) c b = cutLabel (indexSide n) c a)

@[simp] lemma mem_indexCell {n : ℕ} (c : Fin n → Bool) (a b : Fin (n + 1)) :
    b ∈ indexCell c a ↔ cutLabel (indexSide n) c b = cutLabel (indexSide n) c a := by
  simp [indexCell]

lemma indexCell_nonempty {n : ℕ} (c : Fin n → Bool) (a : Fin (n + 1)) :
    (indexCell c a).Nonempty := ⟨a, by simp⟩

noncomputable def cellFirst {n : ℕ} (c : Fin n → Bool) (a : Fin (n + 1)) : Fin (n + 1) :=
  (indexCell c a).min' (indexCell_nonempty c a)

noncomputable def cellLast {n : ℕ} (c : Fin n → Bool) (a : Fin (n + 1)) : Fin (n + 1) :=
  (indexCell c a).max' (indexCell_nonempty c a)

lemma cellFirst_mem {n : ℕ} (c : Fin n → Bool) (a : Fin (n + 1)) :
    cellFirst c a ∈ indexCell c a := Finset.min'_mem _ _

lemma cellLast_mem {n : ℕ} (c : Fin n → Bool) (a : Fin (n + 1)) :
    cellLast c a ∈ indexCell c a := Finset.max'_mem _ _

lemma cellFirst_le {n : ℕ} (c : Fin n → Bool) (a : Fin (n + 1)) : cellFirst c a ≤ a :=
  Finset.min'_le _ _ (by simp)

lemma le_cellLast {n : ℕ} (c : Fin n → Bool) (a : Fin (n + 1)) : a ≤ cellLast c a :=
  Finset.le_max' _ _ (by simp)

/-- Observation fibers have exactly the claimed interval form. -/
lemma indexCell_eq_Icc {n : ℕ} (c : Fin n → Bool) (a : Fin (n + 1)) :
    indexCell c a = Finset.Icc (cellFirst c a) (cellLast c a) := by
  ext b
  constructor
  · intro hb
    exact Finset.mem_Icc.mpr ⟨Finset.min'_le _ _ hb, Finset.le_max' _ _ hb⟩
  · intro hb
    obtain ⟨hfirst, hlast⟩ := Finset.mem_Icc.mp hb
    have hf := (mem_indexCell c a _).mp (cellFirst_mem c a)
    have hl := (mem_indexCell c a _).mp (cellLast_mem c a)
    have hmid := cutLabel_between c (hf.trans hl.symm) hfirst hlast
    exact (mem_indexCell c a b).mpr (hmid.symm.trans hf)

lemma indexCell_eq_of_label_eq {n : ℕ} (c : Fin n → Bool) {a b : Fin (n + 1)}
    (hab : cutLabel (indexSide n) c a = cutLabel (indexSide n) c b) :
    indexCell c a = indexCell c b := by
  ext z
  simp only [mem_indexCell, hab]

lemma cellFirst_eq_of_label_eq {n : ℕ} (c : Fin n → Bool) {a b : Fin (n + 1)}
    (hab : cutLabel (indexSide n) c a = cutLabel (indexSide n) c b) :
    cellFirst c a = cellFirst c b := by
  unfold cellFirst
  simp only [indexCell_eq_of_label_eq c hab]

lemma cellLast_eq_of_label_eq {n : ℕ} (c : Fin n → Bool) {a b : Fin (n + 1)}
    (hab : cutLabel (indexSide n) c a = cutLabel (indexSide n) c b) :
    cellLast c a = cellLast c b := by
  unfold cellLast
  simp only [indexCell_eq_of_label_eq c hab]

end ExactOverlaps.Poisson
