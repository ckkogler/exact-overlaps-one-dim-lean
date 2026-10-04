/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.PairContinuation
public import ExactOverlaps.StoppedConcatenation.FiniteRuleChoice
public import ExactOverlaps.StoppedConcatenation.WordScalars
public import ExactOverlaps.StoppedConcatenation.RuleAssociativity

/-! Finite choice of a future stopping rule depends only on the gap and the head ratio. -/

@[expose] public section

open MeasureTheory
open scoped Classical

namespace ExactOverlaps.StoppedConcatenation

open SelfSimilar Entropy

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

noncomputable def headLabel (S : System ι)
    (z : (Σ n : ℕ, Word ι n) × (Σ n : ℕ, Word ι n)) : (Σ n : ℕ, Word ι n) × ℝ :=
  (z.1, S.totalWordRatio z.2)

noncomputable def headLabelLaw (S : System ι) (G T : BoundedStoppingRule ι) :
    PMF ((Σ n : ℕ, Word ι n) × ℝ) :=
  (independentPair (G.stoppedWordLaw S.alphabetLaw) (T.stoppedWordLaw S.alphabetLaw)).map (headLabel S)

theorem headLabelLaw_support_finite (S : System ι) (G T : BoundedStoppingRule ι) :
    (headLabelLaw S G T).support.Finite := by
  simpa only [headLabelLaw, PMF.support_map] using
    (independentPair_support_finite _ _ (G.stoppedWordLaw_support_finite _)
      (T.stoppedWordLaw_support_finite _)).image (headLabel S)

noncomputable def headContinuation (S : System ι) (G T : BoundedStoppingRule ι)
    (A : (headLabelLaw S G T).support → BoundedStoppingRule ι) : BoundedStoppingRule ι :=
  G.afterPair T (fun z ↦ supportedRule (headLabelLaw S G T) A (headLabel S z))
    (supportedRuleHorizon _ (headLabelLaw_support_finite S G T) A)
      (fun z ↦ supportedRule_horizon_le _ _ A (headLabel S z))

theorem headContinuation_stoppedWordLaw (S : System ι) (G T : BoundedStoppingRule ι)
    (A : (headLabelLaw S G T).support → BoundedStoppingRule ι) :
    (headContinuation S G T A).stoppedWordLaw S.alphabetLaw =
      (jointMixture (independentPair (G.stoppedWordLaw S.alphabetLaw) (T.stoppedWordLaw S.alphabetLaw))
        (fun z ↦ (supportedRule (headLabelLaw S G T) A (headLabel S z)).stoppedWordLaw S.alphabetLaw)).map
          (fun z ↦ Word.concatenate (Word.concatenate z.1.1 z.1.2) z.2) :=
  G.afterPair_stoppedWordLaw T _ _ _ S.alphabetLaw

theorem headContinuation_andThen_law (S : System ι) (G T V : BoundedStoppingRule ι)
    (A : (headLabelLaw S G T).support → BoundedStoppingRule ι) :
    ((headContinuation S G T A).andThen V).stoppedWordLaw S.alphabetLaw =
      (jointMixture (independentPair (G.stoppedWordLaw S.alphabetLaw) (T.stoppedWordLaw S.alphabetLaw))
        (fun z ↦ ((supportedRule (headLabelLaw S G T) A (headLabel S z)).andThen V).stoppedWordLaw S.alphabetLaw)).map
          (fun z ↦ Word.concatenate (Word.concatenate z.1.1 z.1.2) z.2) := by
  rw [headContinuation, G.afterPair_andThen_stoppedWordLaw T V]
  exact G.afterPair_stoppedWordLaw T _ _ _ S.alphabetLaw

theorem headLabelLaw_support (S : System ι) (G T : BoundedStoppingRule ι)
    (b : (headLabelLaw S G T).support) :
    b.val.1 ∈ (G.stoppedWordLaw S.alphabetLaw).support ∧
      ∃ w ∈ (T.stoppedWordLaw S.alphabetLaw).support, S.totalWordRatio w = b.val.2 := by
  obtain ⟨⟨g, w⟩, hgw, he⟩ := (PMF.mem_support_map_iff (headLabel S) _ _).mp b.property
  rw [independentPair_support] at hgw
  have hg := congrArg Prod.fst he
  have hw := congrArg Prod.snd he
  exact ⟨hg ▸ hgw.1, w, hgw.2, hw⟩

theorem headContinuation_ratio_lower (S : System ι) (G T : BoundedStoppingRule ι)
    (A : (headLabelLaw S G T).support → BoundedStoppingRule ι) (L : ℝ)
    (hA : ∀ b, ∀ v ∈ ((A b).stoppedWordLaw S.alphabetLaw).support,
      L / (|S.totalWordRatio b.val.1| * |b.val.2|) < |S.totalWordRatio v|) :
    ∀ u ∈ ((headContinuation S G T A).stoppedWordLaw S.alphabetLaw).support,
      L < |S.totalWordRatio u| := by
  intro u hu
  rw [headContinuation_stoppedWordLaw] at hu
  obtain ⟨⟨⟨g, w⟩, v⟩, hj, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hu
  have hpv : independentPair (G.stoppedWordLaw S.alphabetLaw) (T.stoppedWordLaw S.alphabetLaw) (g, w) *
      (supportedRule (headLabelLaw S G T) A (headLabel S (g, w))).stoppedWordLaw S.alphabetLaw v ≠ 0 := by
    simpa only [PMF.mem_support_iff, jointMixture_apply] using hj
  have hp := left_ne_zero_of_mul hpv
  have hv := right_ne_zero_of_mul hpv
  have hb : headLabel S (g, w) ∈ (headLabelLaw S G T).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨(g, w), hp, rfl⟩
  let b : (headLabelLaw S G T).support := ⟨headLabel S (g, w), hb⟩
  have hsel : supportedRule (headLabelLaw S G T) A (headLabel S (g, w)) = A b :=
    supportedRule_at _ _ b
  rw [hsel] at hv
  have h := hA b v hv
  change L / (|S.totalWordRatio g| * |S.totalWordRatio w|) < |S.totalWordRatio v| at h
  have hc : 0 < |S.totalWordRatio g| * |S.totalWordRatio w| :=
    mul_pos (abs_pos.mpr (S.totalWordRatio_ne_zero g)) (abs_pos.mpr (S.totalWordRatio_ne_zero w))
  rw [← he, S.totalWordRatio_concatenate, S.totalWordRatio_concatenate, abs_mul, abs_mul]
  simpa only [mul_comm] using (div_lt_iff₀ hc).mp h

end ExactOverlaps.StoppedConcatenation
