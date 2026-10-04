module

public import ExactOverlaps.SelfSimilar.RareEventEntropy
public import ExactOverlaps.Entropy.Submodularity
public import Mathlib.Data.Int.Interval

/-!
The entropy difference between integer marginals is bounded by the entropy
of their displacement. A displacement with mostly small magnitude therefore
gives a quantitative comparison even when its exceptional values are large.
-/

@[expose] public section

open scoped Classical

namespace ExactOverlaps.Entropy

theorem abs_snd_entropy_sub_fst_le_displacement_entropy (p : PMF (ℤ × ℤ))
    (hp : p.support.Finite) :
    |finiteEntropy (p.map Prod.snd) (by simpa using hp.image Prod.snd) -
      finiteEntropy (p.map Prod.fst) (by simpa using hp.image Prod.fst)| ≤
      finiteEntropy (p.map (fun z ↦ z.2 - z.1))
        (by simpa using hp.image (fun z ↦ z.2 - z.1)) := by
  have hi₁ : Function.Injective (fun z : ℤ × ℤ ↦ (z.1, z.2 - z.1)) := by
    intro a b h
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
    apply Prod.ext h₁
    omega
  have hi₂ : Function.Injective (fun z : ℤ × ℤ ↦ (z.2, z.2 - z.1)) := by
    intro a b h
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
    apply Prod.ext _ h₁
    omega
  have h₁ := finiteEntropy_pair_map_le p hp Prod.fst (fun z ↦ z.2 - z.1)
  have h₂ := finiteEntropy_pair_map_le p hp Prod.snd (fun z ↦ z.2 - z.1)
  rw [finiteEntropy_map_of_injective p hp hi₁] at h₁
  rw [finiteEntropy_map_of_injective p hp hi₂] at h₂
  have hf := finiteEntropy_map_le p hp Prod.fst
  have hg := finiteEntropy_map_le p hp Prod.snd
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem int_card_Icc_neg_nat (N : ℕ) :
    (Finset.Icc (-(N : ℤ)) (N : ℤ)).card = 2 * N + 1 := by
  have he : (N : ℤ) + 1 - -(N : ℤ) = ((2 * N + 1 : ℕ) : ℤ) := by omega
  rw [Int.card_Icc, he, Int.toNat_natCast]

/-- A bounded integer variable with rare large values has controlled entropy. -/
theorem finiteEntropy_le_of_rare_large_integer (p : PMF ℤ) (hp : p.support.Finite)
    (K N : ℕ) (hglobal : ∀ z ∈ p.support, z ∈ Set.Icc (-(N : ℤ)) N)
    {δ : ℝ}
    (hrare : ((p.map (fun z ↦ decide (z ∉ Set.Icc (-(K : ℤ)) K))) true).toReal ≤ δ) :
    finiteEntropy p hp ≤ Real.log 2 + Real.log (2 * K + 1 : ℝ) +
      δ * Real.log (2 * N + 1 : ℝ) := by
  let f : ℤ → Bool := fun z ↦ decide (z ∉ Set.Icc (-(K : ℤ)) K)
  have hgood : (hp.toFinset.filter (fun a ↦ f a = false)).card ≤ 2 * K + 1 := by
    rw [← int_card_Icc_neg_nat K]
    apply Finset.card_le_card
    intro z hz
    have hz' := (Finset.mem_filter.mp hz).2
    have hzmem : z ∈ Set.Icc (-(K : ℤ)) K := by simpa [f] using hz'
    simpa using hzmem
  have hall : hp.toFinset.card ≤ 2 * N + 1 := by
    rw [← int_card_Icc_neg_nat N]
    apply Finset.card_le_card
    intro z hz
    simpa using hglobal z (by simpa using hz)
  have h := finiteEntropy_le_log_of_rare_event p hp f
    (by omega : 0 < 2 * K + 1) (by omega : 0 < 2 * N + 1) hgood hall hrare
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using h

end ExactOverlaps.Entropy
