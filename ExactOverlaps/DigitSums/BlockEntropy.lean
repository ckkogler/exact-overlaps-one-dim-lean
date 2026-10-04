/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.DigitSums.Counts
public import ExactOverlaps.Entropy.Bounds

/-!
# Entropy bound for sums of finite-valued digits

The sum of m copies of an L-term digit sum has at most
`(m+1)^(L*(K-1))` possible values. This argument does not require independence;
it holds for any probability law on the digit array. Independence is used
elsewhere in the variance-energy argument, not in this counting estimate.
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal Classical

namespace ExactOverlaps.DigitSums

open SelfSimilar Entropy

variable {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι]

/-- Sum the m copies within each digit position, then apply its real coefficient. -/
def blockSum (v : ι → α → ℝ) (a : ι → ℝ) (m : ℕ) (w : ι → Word α m) : ℝ :=
  ∑ j, a j * wordSum (v j) m (w j)

def blockSumFromCounts (v : ι → α → ℝ) (a : ι → ℝ) (a₀ : α) (m : ℕ)
    (c : ι → {x : α // x ≠ a₀} → Fin (m + 1)) : ℝ :=
  ∑ j, a j * sumFromCounts (v j) a₀ m (c j)

lemma blockSum_eq_fromCounts (v : ι → α → ℝ) (a : ι → ℝ) (a₀ : α)
    (m : ℕ) (w : ι → Word α m) :
    blockSum v a m w =
      blockSumFromCounts v a a₀ m (fun j ↦ reducedCounts a₀ m (w j)) := by
  unfold blockSum blockSumFromCounts
  simp_rw [wordSum_eq_sumFromCounts _ a₀]

theorem card_blockSums_le (v : ι → α → ℝ) (a : ι → ℝ) (a₀ : α) (m : ℕ) :
    (Finset.univ.image (blockSum v a m)).card ≤
      (m + 1) ^ (Fintype.card ι * (Fintype.card α - 1)) := by
  classical
  have hsub : Finset.univ.image (blockSum v a m) ⊆
      Finset.univ.image (blockSumFromCounts v a a₀ m) := by
    intro x hx
    obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨fun j ↦ reducedCounts a₀ m (w j), Finset.mem_univ _,
      (blockSum_eq_fromCounts v a a₀ m w).symm.trans hw⟩
  calc
    (Finset.univ.image (blockSum v a m)).card ≤
        (Finset.univ.image (blockSumFromCounts v a a₀ m)).card := Finset.card_le_card hsub
    _ ≤ Fintype.card (ι → {x : α // x ≠ a₀} → Fin (m + 1)) := Finset.card_image_le
    _ = (m + 1) ^ (Fintype.card ι * (Fintype.card α - 1)) := by
      simp [← pow_mul, Nat.mul_comm]

/-- The actual probability law of the weighted digit-array sum. -/
def blockSumLaw (v : ι → α → ℝ) (a : ι → ℝ) (m : ℕ)
    (p : PMF (ι → Word α m)) : PMF ℝ := p.map (blockSum v a m)

omit [DecidableEq α] in
lemma blockSumLaw_support_finite (v : ι → α → ℝ) (a : ι → ℝ) (m : ℕ)
    (p : PMF (ι → Word α m)) : (blockSumLaw v a m p).support.Finite := by
  rw [blockSumLaw, PMF.support_map]
  exact (Set.toFinite _).image _

lemma blockSumLaw_support_card_le (v : ι → α → ℝ) (a : ι → ℝ) (a₀ : α) (m : ℕ)
    (p : PMF (ι → Word α m)) :
    (blockSumLaw_support_finite v a m p).toFinset.card ≤
      (m + 1) ^ (Fintype.card ι * (Fintype.card α - 1)) := by
  classical
  apply (Finset.card_le_card (t := Finset.univ.image (blockSum v a m)) ?_).trans
    (card_blockSums_le v a a₀ m)
  intro x hx
  have hx' : x ∈ (p.map (blockSum v a m)).support := by simpa [blockSumLaw] using hx
  obtain ⟨w, _, hw⟩ := (PMF.mem_support_map_iff _ _ _).mp hx'
  exact Finset.mem_image.mpr ⟨w, Finset.mem_univ _, hw⟩

/-- The exact `L(K-1) log(m+1)` entropy estimate used in the variance-energy lower bound. -/
theorem blockSumLaw_entropy_le (v : ι → α → ℝ) (a : ι → ℝ) (a₀ : α) (m : ℕ)
    (p : PMF (ι → Word α m)) :
    finiteEntropy (blockSumLaw v a m p) (blockSumLaw_support_finite v a m p) ≤
      (Fintype.card ι : ℝ) * (Fintype.card α - 1 : ℕ) * Real.log (m + 1 : ℝ) := by
  have hcard := blockSumLaw_support_card_le v a a₀ m p
  have hpos : (0 : ℝ) < (blockSumLaw_support_finite v a m p).toFinset.card := by
    exact_mod_cast Finset.card_pos.mpr (by simp)
  calc
    finiteEntropy (blockSumLaw v a m p) (blockSumLaw_support_finite v a m p) ≤
        Real.log (blockSumLaw_support_finite v a m p).toFinset.card :=
      finiteEntropy_le_log_card _ _
    _ ≤ Real.log (((m + 1) ^ (Fintype.card ι * (Fintype.card α - 1)) : ℕ) : ℝ) :=
      Real.log_le_log hpos (by exact_mod_cast hcard)
    _ = (Fintype.card ι : ℝ) * (Fintype.card α - 1 : ℕ) * Real.log (m + 1 : ℝ) := by
      rw [Nat.cast_pow, Nat.cast_add, Nat.cast_one, Real.log_pow, Nat.cast_mul]

end ExactOverlaps.DigitSums
