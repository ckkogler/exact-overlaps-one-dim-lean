module

public import ExactOverlaps.Probability.WindowBlocks
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith

/-!
# Endpoint conditions for a real window block

An ordered block is exactly the set selected by a half-open window when its
two endpoint atoms lie inside and the existing neighboring atoms lie outside.
The strict and weak inequalities retain the actual window convention.
-/

@[expose] public section

open MeasureTheory Set
open scoped Classical

namespace ExactOverlaps.Poisson

def windowBlockPattern {n : ℕ} (x : Fin (n + 1) → ℝ) (a r : ℝ)
    (i j : Fin (n + 1)) : Prop :=
  a ≤ x i ∧ x j < a + r ∧
    (∀ k : Fin n, k.val + 1 = i.val → x k.castSucc < a) ∧
    (∀ k : Fin n, k.val = j.val → a + r ≤ x k.succ)

lemma windowIndices_eq_Icc_iff {n : ℕ} (x : Fin (n + 1) → ℝ) (hx : Monotone x)
    (a r : ℝ) (i j : Fin (n + 1)) (hij : i ≤ j) :
    windowIndices x a r = Finset.Icc i j ↔ windowBlockPattern x a r i j := by
  constructor
  · intro h
    have hi : x i ∈ Ico a (a + r) := by
      rw [← mem_windowIndices, h]
      exact Finset.mem_Icc.mpr ⟨le_rfl, hij⟩
    have hj : x j ∈ Ico a (a + r) := by
      rw [← mem_windowIndices, h]
      exact Finset.mem_Icc.mpr ⟨hij, le_rfl⟩
    refine ⟨hi.1, hj.2, ?_, ?_⟩
    · intro k hk
      have hnot : x k.castSucc ∉ Ico a (a + r) := by
        rw [← mem_windowIndices, h, Finset.mem_Icc]
        intro hm
        have hm' : i.val ≤ k.val := hm.1
        omega
      have hki : k.castSucc ≤ i := by change k.val ≤ i.val; omega
      have hupper : x k.castSucc < a + r := (hx hki).trans_lt hi.2
      by_contra hlow
      exact hnot ⟨le_of_not_gt hlow, hupper⟩
    · intro k hk
      have hnot : x k.succ ∉ Ico a (a + r) := by
        rw [← mem_windowIndices, h, Finset.mem_Icc]
        intro hm
        have hm' : k.val + 1 ≤ j.val := hm.2
        omega
      have hjk : j ≤ k.succ := by change j.val ≤ k.val + 1; omega
      have hlower : a ≤ x k.succ := hj.1.trans (hx hjk)
      by_contra hupper
      exact hnot ⟨hlower, lt_of_not_ge hupper⟩
  · rintro ⟨hleft, hright, hprev, hnext⟩
    ext z
    rw [mem_windowIndices, Finset.mem_Icc]
    constructor
    · intro hz
      constructor
      · by_contra hiz
        have hzi : z.val < i.val := by simpa using lt_of_not_ge hiz
        let k : Fin n := ⟨i.val - 1, by have hi := i.isLt; omega⟩
        have hk : k.val + 1 = i.val := by dsimp [k]; omega
        have hzk : z ≤ k.castSucc := by change z.val ≤ k.val; omega
        have hbound := (hx hzk).trans_lt (hprev k hk)
        exact (not_lt_of_ge hz.1) hbound
      · by_contra hzj
        have hjz : j.val < z.val := by simpa using lt_of_not_ge hzj
        let k : Fin n := ⟨j.val, by have hz := z.isLt; omega⟩
        have hkz : k.succ ≤ z := by change k.val + 1 ≤ z.val; dsimp [k]; omega
        have hbound := (hnext k rfl).trans (hx hkz)
        exact (not_lt_of_ge hbound) hz.2
    · rintro ⟨hiz, hzj⟩
      exact ⟨hleft.trans (hx hiz), (hx hzj).trans_lt hright⟩

end ExactOverlaps.Poisson
