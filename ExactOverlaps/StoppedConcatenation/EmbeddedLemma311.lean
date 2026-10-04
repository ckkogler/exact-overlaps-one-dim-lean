/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.Lemma311
public import ExactOverlaps.StoppedConcatenation.EmbeddingWitness

/-! The stopping-block inequality together with an explicit bounded start for every embedded block. -/

@[expose] public section

open MeasureTheory
open scoped Classical

namespace ExactOverlaps.SelfSimilar.System

open StoppedConcatenation ConvolutionDisintegration

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem exists_stopped_concatenation_embedded_start (S : System ι) :
    ∀ (m : ℕ) (τ : Fin (m + 1) → BoundedStoppingRule ι) (s : Fin (m + 1) → ℝ),
    (∀ j, 0 < s j) →
    (∀ i j, i < j → ∀ w ∈ ((τ i).stoppedWordLaw S.alphabetLaw).support,
      s i ≤ S.rhoMin * s j * |S.totalWordRatio w|) →
    ∀ (r : ℝ), 0 < r → r ≤ s 0 →
    ∃ A : BoundedStoppingRule ι,
      meanConditionalMapW ((A.andThen (τ (Fin.last m))).stoppedWordLaw S.alphabetLaw)
        ((A.andThen (τ (Fin.last m))).stoppedWordLaw_support_finite _)
        S.totalWordRatio S.totalWordTranslation r ≤
          ∏ j : Fin (m + 1),
            (meanConditionalMapW ((τ j).stoppedWordLaw S.alphabetLaw)
              ((τ j).stoppedWordLaw_support_finite _) S.totalWordRatio S.totalWordTranslation (s j)) ^
                (S.rhoMin ^ 2) ∧
      (∀ a ∈ (A.stoppedWordLaw S.alphabetLaw).support,
        S.rhoMin * r / s (Fin.last m) < |S.totalWordRatio a|) ∧
      HasBlockStarts S m τ A := by
  intro m
  induction m with
  | zero =>
    intro τ s hs hsep r hr hrs
    let G := S.ratioCrossingRule (r / s 0) (div_pos hr (hs 0))
    refine ⟨G, ?_, ?_, hasBlockStarts_single S τ G⟩
    · change meanConditionalMapW ((G.andThen (τ 0)).stoppedWordLaw S.alphabetLaw)
        ((G.andThen (τ 0)).stoppedWordLaw_support_finite _) S.totalWordRatio S.totalWordTranslation r ≤
        ∏ j : Fin 1, (meanConditionalMapW ((τ j).stoppedWordLaw S.alphabetLaw)
          ((τ j).stoppedWordLaw_support_finite _) S.totalWordRatio S.totalWordTranslation (s j)) ^
            (S.rhoMin ^ 2)
      rw [Fin.prod_univ_one]
      exact ConditionalW.single_block_W_le S (τ 0) hr (hs 0) hrs
    · intro a ha
      have h := (S.ratioCrossingWordLaw_bounds (r / s 0) (div_pos hr (hs 0))
        ((div_le_one (hs 0)).2 hrs) ⟨a, ha⟩).1
      change S.rhoMin * (r / s 0) < |S.totalWordRatio a| at h
      change S.rhoMin * r / s 0 < |S.totalWordRatio a|
      simpa only [mul_div_assoc] using h
  | succ m ih =>
    intro τ s hs hsep r hr hrs
    let τ' : Fin (m + 1) → BoundedStoppingRule ι := fun j ↦ τ j.succ
    let s' : Fin (m + 1) → ℝ := fun j ↦ s j.succ
    have hs' : ∀ j, 0 < s' j := fun j ↦ hs j.succ
    have hsep' : ∀ i j : Fin (m + 1), i < j →
        ∀ w ∈ ((τ' i).stoppedWordLaw S.alphabetLaw).support,
          s' i ≤ S.rhoMin * s' j * |S.totalWordRatio w| := by
      intro i j hij
      exact hsep i.succ j.succ (Fin.succ_lt_succ_iff.mpr hij)
    let G := S.ratioCrossingRule (r / s 0) (div_pos hr (hs 0))
    have hsep0 : ∀ w ∈ ((τ 0).stoppedWordLaw S.alphabetLaw).support,
        s 0 ≤ S.rhoMin * s' 0 * |S.totalWordRatio w| :=
      hsep 0 (Fin.succ 0) (by simp)
    have hlocal (b : (headLabelLaw S G (τ 0)).support) :
        0 < r / (|S.totalWordRatio b.val.1| * |b.val.2|) ∧
          r / (|S.totalWordRatio b.val.1| * |b.val.2|) ≤ s' 0 :=
      head_next_scale_le S (τ 0) hr (hs 0) hrs hsep0 b
    choose A hA using (fun b : (headLabelLaw S G (τ 0)).support ↦
      ih τ' s' hs' hsep' (r / (|S.totalWordRatio b.val.1| * |b.val.2|))
        (hlocal b).1 (hlocal b).2)
    let cap : ℝ := ∏ j : Fin (m + 1),
      (meanConditionalMapW ((τ' j).stoppedWordLaw S.alphabetLaw)
        ((τ' j).stoppedWordLaw_support_finite _) S.totalWordRatio S.totalWordTranslation (s' j)) ^
          (S.rhoMin ^ 2)
    have hcap : 0 ≤ cap := by
      apply Finset.prod_nonneg
      intro j _
      exact Real.rpow_nonneg (meanConditionalMapW_nonneg _ _ _ _ (hs' j).le) _
    refine ⟨headContinuation S G (τ 0) A, ?_, ?_,
      hasBlockStarts_head S m τ G A (fun b ↦ (hA b).2.2)⟩
    · have hcost (b : (headLabelLaw S G (τ 0)).support) :
          meanConditionalMapW (((A b).andThen (τ (Fin.last (m + 1)))).stoppedWordLaw S.alphabetLaw)
            (((A b).andThen (τ (Fin.last (m + 1)))).stoppedWordLaw_support_finite _)
            S.totalWordRatio S.totalWordTranslation
            (r / (|S.totalWordRatio b.val.1| * |b.val.2|)) ≤ cap := (hA b).1
      have h := ConditionalW.head_step_W_le S (τ 0) (τ (Fin.last (m + 1)))
        hr (hs 0) hrs hcap A hcost
      change meanConditionalMapW _ _ _ _ r ≤ _ at h
      rw [Fin.prod_univ_succ]
      simpa only [cap, τ', s', mul_comm] using h
    · apply headContinuation_ratio_lower S G (τ 0) A (S.rhoMin * r / s (Fin.last (m + 1)))
      intro b v hv
      have h := (hA b).2.1 v hv
      change S.rhoMin * (r / (|S.totalWordRatio b.val.1| * |b.val.2|)) /
        s (Fin.last (m + 1)) < |S.totalWordRatio v| at h
      convert h using 1
      ring

end ExactOverlaps.SelfSimilar.System
