/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.WordMeasurability
public import ExactOverlaps.SelfSimilar.CodingSeries

/-! Exact signed prefix ratios and the deterministic contraction properties used in alignment. -/

@[expose] public section

open MeasureTheory

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι]

theorem wordRatio_read (S : System ι) (n : ℕ) (ω : ℕ → ι) :
    S.wordRatio n (Word.read n ω) = S.prefixRatio n ω := by
  induction n generalizing ω with
  | zero => simp [wordRatio, wordMap, prefixRatio, RealSimilarity.identity]
  | succ n ih =>
    change (S.map (ω 0)).ratio * S.wordRatio n (Word.read n (Bernoulli.shift ω)) = _
    rw [ih, S.prefixRatio_succ_shift]

theorem prefixRatio_nonzero (S : System ι) (n : ℕ) (ω : ℕ → ι) : S.prefixRatio n ω ≠ 0 := by
  rw [← S.wordRatio_read]
  exact S.wordRatio_ne_zero _ _

theorem abs_prefixRatio_succ_lt (S : System ι) (n : ℕ) (ω : ℕ → ι) :
    |S.prefixRatio (n + 1) ω| < |S.prefixRatio n ω| := by
  rw [S.prefixRatio_succ, abs_mul]
  exact mul_lt_of_lt_one_right (abs_pos.mpr (S.prefixRatio_nonzero n ω)) (S.contracting _)

theorem abs_prefixRatio_antitone (S : System ι) (ω : ℕ → ι) :
    Antitone (fun n ↦ |S.prefixRatio n ω|) :=
  antitone_nat_of_succ_le (fun n ↦ (S.abs_prefixRatio_succ_lt n ω).le)

theorem exists_uniform_ratio_crossing (S : System ι) {r : ℝ} (hr : 0 < r) :
    ∃ N : ℕ, ∀ ω : ℕ → ι, |S.prefixRatio N ω| ≤ r := by
  obtain ⟨c, M, hc, hc1, hM, hmax, hshift⟩ := S.exists_uniform_bounds
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hr hc1
  exact ⟨N, fun ω ↦ (S.abs_prefixRatio_le hc.le hmax N ω).trans hN.le⟩

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem measurable_prefixRatio_at (S : System ι) (n : ℕ) :
    Measurable[StoppedConcatenation.incrementFiltration (ι := ι) n] (S.prefixRatio n) := by
  have he : S.prefixRatio n = S.wordRatio n ∘ Word.read n :=
    funext (fun ω ↦ (S.wordRatio_read n ω).symm)
  rw [he]
  exact (measurable_of_finite (S.wordRatio n)).comp (Word.measurable_read_at n)

end ExactOverlaps.SelfSimilar.System
