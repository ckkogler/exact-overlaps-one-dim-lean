/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic

/-!
# Dense windows and translated good scales

Double counting gives a corrected shifted-window estimate. Requiring both a
scale and its translate to be good costs two missing-density terms.
-/

@[expose] public section

open scoped BigOperators

namespace ExactOverlaps.Entropy

lemma sum_window_card_le (I J : Finset ℤ) (m : ℕ) :
    (∑ i ∈ I, (J.filter (fun j ↦ i ≤ j ∧ j < i + m)).card) ≤ m * J.card := by
  have he : (∑ i ∈ I, (J.filter (fun j ↦ i ≤ j ∧ j < i + m)).card) =
      ∑ j ∈ J, (I.filter (fun i ↦ i ≤ j ∧ j < i + m)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  rw [he]
  calc
    _ ≤ ∑ _j ∈ J, m := by
      apply Finset.sum_le_sum
      intro j _
      have hsub : I.filter (fun i ↦ i ≤ j ∧ j < i + m) ⊆ Finset.Ioc (j - m) j := by
        intro i hi
        simp only [Finset.mem_filter] at hi
        simp only [Finset.mem_Ioc]
        omega
      have h := Finset.card_le_card hsub
      simpa using h
    _ = _ := by simp [Nat.mul_comm]

lemma window_shift_pair_card (J : Finset ℤ) (i : ℤ) (m ℓ : ℕ) :
    2 * (J.filter (fun j ↦ i ≤ j ∧ j < i + m)).card ≤ m + ℓ +
      ((J.filter (fun j ↦ j + (ℓ : ℤ) ∈ J)).filter (fun j ↦ i ≤ j ∧ j < i + m)).card := by
  let A := J.filter (fun j ↦ i ≤ j ∧ j < i + m)
  let B := A.image (fun j ↦ j - (ℓ : ℤ))
  have hB : B.card = A.card := Finset.card_image_of_injective _ (fun _ _ h ↦ by omega)
  have hu : A ∪ B ⊆ Finset.Ico (i - ℓ) (i + m) := by
    intro j hj
    rcases Finset.mem_union.mp hj with hj | hj
    · have h := (Finset.mem_filter.mp hj).2
      simp only [Finset.mem_Ico]
      omega
    · rcases Finset.mem_image.mp hj with ⟨a, ha, rfl⟩
      have h := (Finset.mem_filter.mp ha).2
      simp only [Finset.mem_Ico]
      omega
  have hucard : (A ∪ B).card ≤ m + ℓ := by
    have h := Finset.card_le_card hu
    have hlen : (Finset.Ico (i - ℓ) (i + m)).card = m + ℓ := by
      rw [Int.card_Ico]
      omega
    simpa only [hlen] using h
  have hi : A ∩ B ⊆
      (J.filter (fun j ↦ j + (ℓ : ℤ) ∈ J)).filter (fun j ↦ i ≤ j ∧ j < i + m) := by
    intro j hj
    obtain ⟨hjA, hjB⟩ := Finset.mem_inter.mp hj
    obtain ⟨a, ha, haj⟩ := Finset.mem_image.mp hjB
    have hja : j + (ℓ : ℤ) = a := by omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hjA).1, hja ▸ (Finset.mem_filter.mp ha).1⟩,
      (Finset.mem_filter.mp hjA).2⟩
  have hicard := Finset.card_le_card hi
  have hcard := Finset.card_union_add_card_inter A B
  change 2 * A.card ≤ _
  omega

/-- Dense windows force many good scales whose translate is also good. -/
theorem shifted_good_scales_card (I J : Finset ℤ) (m ℓ : ℕ) (δ : ℝ)
    (hdense : ∀ i ∈ I, (1 - δ) * m ≤ (J.filter (fun j ↦ i ≤ j ∧ j < i + m)).card) :
    ((1 - 2 * δ) * m - ℓ) * I.card ≤
      (m : ℝ) * (J.filter (fun j ↦ j + (ℓ : ℤ) ∈ J)).card := by
  have hlocal : ∀ i ∈ I, (1 - 2 * δ) * m - ℓ ≤
      (((J.filter (fun j ↦ j + (ℓ : ℤ) ∈ J)).filter (fun j ↦ i ≤ j ∧ j < i + m)).card : ℝ) := by
    intro i hi
    have h := window_shift_pair_card J i m ℓ
    have h' : 2 * ((J.filter (fun j ↦ i ≤ j ∧ j < i + m)).card : ℝ) ≤
        (m : ℝ) + ℓ +
          ((J.filter (fun j ↦ j + (ℓ : ℤ) ∈ J)).filter (fun j ↦ i ≤ j ∧ j < i + m)).card := by
      exact_mod_cast h
    have hd := hdense i hi
    nlinarith
  have hs := Finset.sum_le_sum hlocal
  have hu := sum_window_card_le I (J.filter (fun j ↦ j + (ℓ : ℤ) ∈ J)) m
  have hu' : (∑ i ∈ I,
      (((J.filter (fun j ↦ j + (ℓ : ℤ) ∈ J)).filter (fun j ↦ i ≤ j ∧ j < i + m)).card : ℝ)) ≤
      (m : ℝ) * (J.filter (fun j ↦ j + (ℓ : ℤ) ∈ J)).card := by exact_mod_cast hu
  simp only [Finset.sum_const, nsmul_eq_mul] at hs
  nlinarith [hs.trans hu']

end ExactOverlaps.Entropy
