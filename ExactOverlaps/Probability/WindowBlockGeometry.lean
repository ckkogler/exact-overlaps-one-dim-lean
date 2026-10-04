module

public import ExactOverlaps.Probability.WindowBlockPatterns
public import ExactOverlaps.Probability.PoissonBoundaryKernels
import Mathlib.Tactic.SplitIfs

/-!
# Lebesgue geometry of finite-support window blocks

The origin set selecting a fixed block is an explicit half-open interval.
Interior and boundary blocks retain their distinct neighboring conditions.
-/

@[expose] public section

open MeasureTheory Set
open scoped Classical

namespace ExactOverlaps.Poisson

def windowOrigins {n : ℕ} (x : Fin (n + 1) → ℝ) (r : ℝ)
    (i j : Fin (n + 1)) : Set ℝ :=
  {a | windowIndices x a r = Finset.Icc i j}

lemma windowOrigins_interior {n : ℕ} (x : Fin (n + 1) → ℝ) (hx : Monotone x)
    (r : ℝ) (i j : Fin n) (hij : i.succ ≤ j.castSucc) :
    windowOrigins x r i.succ j.castSucc =
      Ioc (max (x i.castSucc) (x j.castSucc - r))
        (min (x i.succ) (x j.succ - r)) := by
  ext a
  rw [windowOrigins, mem_ofPred_eq, windowIndices_eq_Icc_iff x hx _ _ _ _ hij]
  simp only [windowBlockPattern, mem_Ioc, max_lt_iff, le_min_iff]
  constructor
  · rintro ⟨hl, hr, hp, hn⟩
    exact ⟨⟨hp i rfl, by linarith⟩, hl, by linarith [hn j rfl]⟩
  · rintro ⟨⟨hp, hr⟩, hl, hn⟩
    refine ⟨hl, by linarith, ?_, ?_⟩
    · intro k hk
      have he : k = i := Fin.ext (by simpa using Nat.add_right_cancel hk)
      simpa [he] using hp
    · intro k hk
      have he : k = j := Fin.ext hk
      subst k
      linarith

lemma windowOrigins_left {n : ℕ} (x : Fin (n + 1) → ℝ) (hx : Monotone x)
    (r : ℝ) (j : Fin n) :
    windowOrigins x r 0 j.castSucc =
      Ioc (x j.castSucc - r) (min (x 0) (x j.succ - r)) := by
  ext a
  rw [windowOrigins, mem_ofPred_eq,
    windowIndices_eq_Icc_iff x hx _ _ _ _ (Fin.zero_le _)]
  simp only [windowBlockPattern, mem_Ioc, le_min_iff]
  constructor
  · rintro ⟨hl, hr, _, hn⟩
    exact ⟨by linarith, hl, by linarith [hn j rfl]⟩
  · rintro ⟨hr, hl, hn⟩
    refine ⟨hl, by linarith, ?_, ?_⟩
    · intro k hk
      have : k.val + 1 = 0 := hk
      omega
    · intro k hk
      have he : k = j := Fin.ext hk
      subst k
      linarith

lemma windowOrigins_right {n : ℕ} (x : Fin (n + 1) → ℝ) (hx : Monotone x)
    (r : ℝ) (i : Fin n) :
    windowOrigins x r i.succ (Fin.last n) =
      Ioc (max (x i.castSucc) (x (Fin.last n) - r)) (x i.succ) := by
  ext a
  rw [windowOrigins, mem_ofPred_eq,
    windowIndices_eq_Icc_iff x hx _ _ _ _ (Fin.le_last _)]
  simp only [windowBlockPattern, mem_Ioc, max_lt_iff]
  constructor
  · rintro ⟨hl, hr, hp, _⟩
    exact ⟨⟨hp i rfl, by linarith⟩, hl⟩
  · rintro ⟨⟨hp, hr⟩, hl⟩
    refine ⟨hl, by linarith, ?_, ?_⟩
    · intro k hk
      have he : k = i := Fin.ext (by simpa using Nat.add_right_cancel hk)
      simpa [he] using hp
    · intro k hk
      have : k.val = n := hk
      have := k.isLt
      omega

lemma windowOrigins_full {n : ℕ} (x : Fin (n + 1) → ℝ) (hx : Monotone x)
    (r : ℝ) :
    windowOrigins x r 0 (Fin.last n) = Ioc (x (Fin.last n) - r) (x 0) := by
  ext a
  rw [windowOrigins, mem_ofPred_eq,
    windowIndices_eq_Icc_iff x hx _ _ _ _ (Fin.zero_le _)]
  simp only [windowBlockPattern, mem_Ioc]
  constructor
  · rintro ⟨hl, hr, _, _⟩
    exact ⟨by linarith, hl⟩
  · rintro ⟨hr, hl⟩
    refine ⟨hl, by linarith, ?_, ?_⟩
    · intro k hk
      have : k.val + 1 = 0 := hk
      omega
    · intro k hk
      have : k.val = n := hk
      have := k.isLt
      omega

lemma volume_windowOrigins_interior {n : ℕ} (x : Fin (n + 1) → ℝ) (hx : Monotone x)
    (r : ℝ) (i j : Fin n) (hij : i.succ ≤ j.castSucc) :
    volume (windowOrigins x r i.succ j.castSucc) =
      ENNReal.ofReal (cellOffsetLength (x j.castSucc - x i.succ)
        (x i.succ - x i.castSucc) (x j.succ - x j.castSucc) r) := by
  rw [windowOrigins_interior x hx r i j hij, Real.volume_Ioc]
  have hi : x i.castSucc ≤ x i.succ := hx (by change i.val ≤ i.val + 1; omega)
  have hj : x j.castSucc ≤ x j.succ := hx (by change j.val ≤ j.val + 1; omega)
  rw [cellOffsetLength_eq_intersection_length (sub_nonneg.mpr hi) (sub_nonneg.mpr hj)]
  have he : max (min (x i.succ) (x j.succ - r) -
      max (x i.castSucc) (x j.castSucc - r)) 0 =
      max (min 0 (x j.castSucc - x i.succ + (x j.succ - x j.castSucc) - r) -
        max (-(x i.succ - x i.castSucc)) (x j.castSucc - x i.succ - r)) 0 := by
    simp only [min_def, max_def]
    split_ifs <;> linarith
  rw [← he]
  simp

lemma volume_windowOrigins_left {n : ℕ} (x : Fin (n + 1) → ℝ) (hx : Monotone x)
    (r : ℝ) (j : Fin n) :
    volume (windowOrigins x r 0 j.castSucc) =
      ENNReal.ofReal (boundaryOffsetLength (x j.castSucc - x 0)
        (x j.succ - x j.castSucc) r) := by
  rw [windowOrigins_left x hx r j, Real.volume_Ioc]
  have hj : x j.castSucc ≤ x j.succ := hx (by change j.val ≤ j.val + 1; omega)
  rw [boundaryOffsetLength_eq_left_length (sub_nonneg.mpr hj)]
  have he : max (min (x 0) (x j.succ - r) - (x j.castSucc - r)) 0 =
      max (min 0 (x j.castSucc - x 0 + (x j.succ - x j.castSucc) - r) -
        (x j.castSucc - x 0 - r)) 0 := by
    simp only [min_def, max_def]
    split_ifs <;> linarith
  rw [← he]
  simp

lemma volume_windowOrigins_right {n : ℕ} (x : Fin (n + 1) → ℝ) (hx : Monotone x)
    (r : ℝ) (i : Fin n) :
    volume (windowOrigins x r i.succ (Fin.last n)) =
      ENNReal.ofReal (boundaryOffsetLength (x (Fin.last n) - x i.succ)
        (x i.succ - x i.castSucc) r) := by
  rw [windowOrigins_right x hx r i, Real.volume_Ioc]
  have hi : x i.castSucc ≤ x i.succ := hx (by change i.val ≤ i.val + 1; omega)
  rw [boundaryOffsetLength_eq_right_length (sub_nonneg.mpr hi)]
  have he : max (x i.succ - max (x i.castSucc) (x (Fin.last n) - r)) 0 =
      max (-max (-(x i.succ - x i.castSucc)) (x (Fin.last n) - x i.succ - r)) 0 := by
    simp only [max_def]
    split_ifs <;> linarith
  rw [← he]
  simp

lemma volume_windowOrigins_full {n : ℕ} (x : Fin (n + 1) → ℝ) (hx : Monotone x)
    (r : ℝ) :
    volume (windowOrigins x r 0 (Fin.last n)) =
      ENNReal.ofReal (max (r - (x (Fin.last n) - x 0)) 0) := by
  rw [windowOrigins_full x hx r, Real.volume_Ioc]
  have he : x 0 - (x (Fin.last n) - r) = r - (x (Fin.last n) - x 0) := by ring
  rw [he]
  simp

end ExactOverlaps.Poisson
