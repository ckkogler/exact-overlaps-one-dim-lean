module

public import ExactOverlaps.Probability.CutBlockVariance
public import ExactOverlaps.Probability.PoissonMixedPatterns
import Lean.Elab.Tactic.Omega

/-!
# Probability of selecting a contiguous block

The exact block event is an independent mixed pattern: no internal gap is
cut, while each existing neighboring gap is cut. Its probability is therefore
the block-diameter survival factor times the neighboring cut factors.
-/

@[expose] public section

open scoped BigOperators Classical

namespace ExactOverlaps.Poisson

def internalGaps {n : ℕ} (a b : Fin (n + 1)) : Finset (Fin n) :=
  Finset.univ.filter (fun k ↦ a.val ≤ k.val ∧ k.val < b.val)

def neighboringGaps {n : ℕ} (a b : Fin (n + 1)) : Finset (Fin n) :=
  Finset.univ.filter (fun k ↦ k.val + 1 = a.val ∨ k.val = b.val)

lemma internalGaps_disjoint_neighboringGaps {n : ℕ} (a b : Fin (n + 1)) :
    Disjoint (internalGaps a b) (neighboringGaps a b) := by
  apply Finset.disjoint_left.mpr
  intro k hi hn
  simp only [internalGaps, neighboringGaps, Finset.mem_filter, Finset.mem_univ, true_and] at hi hn
  omega

lemma blockPattern_iff_mixed {n : ℕ} (c : Fin n → Bool) (a b : Fin (n + 1))
    (hab : a ≤ b) :
    blockPattern c a b ↔
      (∀ k ∈ internalGaps a b, c k = false) ∧
        (∀ k ∈ neighboringGaps a b, c k = true) := by
  constructor
  · rintro ⟨_, hi, hl, hr⟩
    constructor
    · intro k hk
      obtain ⟨_, hka, hkb⟩ := Finset.mem_filter.mp hk
      exact hi k hka hkb
    · intro k hk
      rcases (Finset.mem_filter.mp hk).2 with hk | hk
      · exact hl k hk
      · exact hr k hk
  · rintro ⟨hi, hn⟩
    refine ⟨hab, ?_, ?_, ?_⟩
    · intro k hka hkb
      exact hi k (by simp [internalGaps, hka, hkb])
    · intro k hk
      exact hn k (by simp [neighboringGaps, hk])
    · intro k hk
      exact hn k (by simp [neighboringGaps, hk])

lemma blockWeight_eq_mixed_product {n : ℕ} (d : Fin n → ℝ) (t : ℝ)
    (a b : Fin (n + 1)) (hab : a ≤ b) :
    blockWeight d t a b = Real.exp (-((∑ k ∈ internalGaps a b, d k) * t)) *
      ∏ k ∈ neighboringGaps a b, (1 - Real.exp (-(d k * t))) := by
  unfold blockWeight
  have h := sum_cutWeight_mixedPattern d t (internalGaps a b) (neighboringGaps a b)
    (internalGaps_disjoint_neighboringGaps a b)
  refine Eq.trans ?_ h
  apply Finset.sum_congr (by ext c; simp)
  intro c _
  simp only [blockPattern_iff_mixed c a b hab]
  split_ifs <;> rfl

/-- For an ordered real statistic the internal survival factor is the block diameter. -/
lemma ordered_blockWeight_eq {n : ℕ} (x : ℕ → ℝ) (t : ℝ)
    (a b : Fin (n + 1)) (hab : a ≤ b) :
    blockWeight (orderedGapLength x n) t a b = Real.exp (-((x b.val - x a.val) * t)) *
      ∏ k ∈ neighboringGaps a b, (1 - Real.exp (-(orderedGapLength x n k * t))) := by
  rw [blockWeight_eq_mixed_product _ t a b hab]
  have he : internalGaps a b = separatingCuts (indexSide n) a b :=
    (separatingCuts_indexSide_of_le a b hab).symm
  rw [he, sum_orderedGapLength_of_le x n a b hab]

end ExactOverlaps.Poisson
