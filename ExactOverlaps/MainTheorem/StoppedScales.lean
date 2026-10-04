/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.MainTheorem.RecursiveScales
public import ExactOverlaps.StoppedConcatenation.MinimumRatio
public import ExactOverlaps.StoppedConcatenation.StoppedWordLaw

/-!
Recursive choices and reversal for genuine stopped-word laws. Every separation
condition is asserted on the actual positive-probability stopped words.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace ExactOverlaps.MainTheorem

open SelfSimilar StoppedConcatenation

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem exists_stopped_scale_sequence (S : System ι)
    (Q : BoundedStoppingRule ι → ℝ → Prop)
    (h : ∀ ε : ℝ, 0 < ε → ∃ T : BoundedStoppingRule ι, ∃ r : ℝ,
      0 < r ∧ Q T r ∧ ∀ w ∈ (T.stoppedWordLaw S.alphabetLaw).support,
        r < ε * |S.wordRatio w.1 w.2|) :
    ∃ T : ℕ → BoundedStoppingRule ι, ∃ r : ℕ → ℝ,
      (∀ n, 0 < r n) ∧ (∀ n, Q (T n) (r n)) ∧ StrictAnti r ∧
      Tendsto r atTop (𝓝 0) ∧ ∀ n,
        ∀ w ∈ ((T (n + 1)).stoppedWordLaw S.alphabetLaw).support,
          r (n + 1) < S.rhoMin * r n * |S.wordRatio w.1 w.2| := by
  obtain ⟨T, r, hr, hQ, _, hsep⟩ := exists_separated_sequence Q
    (fun T ε r ↦ ∀ w ∈ (T.stoppedWordLaw S.alphabetLaw).support,
      r < ε * |S.wordRatio w.1 w.2|) S.rhoMin_pos h
  have hratio (w : Σ n : ℕ, Word ι n) : |S.wordRatio w.1 w.2| ≤ 1 := by
    simpa only [one_pow] using
      S.abs_wordRatio_le_pow (c := 1) zero_le_one (fun i ↦ (S.contracting i).le) w.1 w.2
  have hstep (n : ℕ) : r (n + 1) < S.rhoMin * r n := by
    obtain ⟨w, hw⟩ := ((T (n + 1)).stoppedWordLaw S.alphabetLaw).support_nonempty
    exact (hsep n w hw).trans_le
      (mul_le_of_le_one_right (mul_pos S.rhoMin_pos (hr n)).le (hratio w))
  have hanti : StrictAnti r := by
    apply strictAnti_nat_of_succ_lt
    intro n
    exact (hstep n).trans (by
      simpa only [one_mul] using mul_lt_mul_of_pos_right S.rhoMin_lt_one (hr n))
  exact ⟨T, r, hr, hQ, hanti,
    geometrically_decreasing_scales_tendsto_zero S.rhoMin_pos S.rhoMin_lt_one r hr
      (fun n ↦ (hstep n).le), hsep⟩

/-- The first n+1 decreasing scales, read backwards, have the required strict order. -/
theorem reversed_scales_strictMono {r : ℕ → ℝ} (hr : StrictAnti r) (n : ℕ) :
    StrictMono (fun j : Fin (n + 1) ↦ r (n - j)) := by
  intro i j hij
  apply hr
  have hi := i.isLt
  have hj := j.isLt
  have hij' : (i : ℕ) < j := hij
  omega

/-- Adjacent reversed blocks satisfy exactly the positive-atom separation
required by the concatenation lemma. -/
theorem reversed_stopped_separation (S : System ι)
    (T : ℕ → BoundedStoppingRule ι) (r : ℕ → ℝ)
    (hsep : ∀ n, ∀ w ∈ ((T (n + 1)).stoppedWordLaw S.alphabetLaw).support,
      r (n + 1) < S.rhoMin * r n * |S.wordRatio w.1 w.2|)
    (n : ℕ) (j : Fin n)
    (w : Σ k : ℕ, Word ι k)
    (hw : w ∈ ((T (n - j)).stoppedWordLaw S.alphabetLaw).support) :
    r (n - j) ≤ S.rhoMin * r (n - ((j : ℕ) + 1)) * |S.wordRatio w.1 w.2| := by
  have he : n - ((j : ℕ) + 1) + 1 = n - j := by omega
  have h := hsep (n - ((j : ℕ) + 1))
  rw [he] at h
  exact (h w hw).le

end ExactOverlaps.MainTheorem
