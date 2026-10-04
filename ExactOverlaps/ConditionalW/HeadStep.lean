/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.ConditionalW.GapAverage
public import ExactOverlaps.ConditionalW.UniformCap
public import ExactOverlaps.StoppedConcatenation.ConditionalPushforward
public import ExactOverlaps.StoppedConcatenation.ScaleAlignment

/-! The concrete conditional W estimate for a crossing gap and an adaptive continuation. -/

@[expose] public section

open scoped Classical

namespace ExactOverlaps.ConditionalW

open SelfSimilar Entropy FiniteProbability ConvolutionDisintegration StoppedConcatenation

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem crossing_head_W_le (S : System ι) (T : BoundedStoppingRule ι)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hrs : r ≤ s) :
    let G := S.ratioCrossingRule (r / s) (div_pos hr hs)
    meanConditionalMapW
      (independentPair (G.stoppedWordLaw S.alphabetLaw) (T.stoppedWordLaw S.alphabetLaw))
      (independentPair_support_finite _ _ (G.stoppedWordLaw_support_finite _)
        (T.stoppedWordLaw_support_finite _))
      (headLabel S)
      (fun z ↦ S.totalWordTranslation z.1 + S.totalWordRatio z.1 * S.totalWordTranslation z.2) r ≤
      (meanConditionalMapW (T.stoppedWordLaw S.alphabetLaw) (T.stoppedWordLaw_support_finite _)
        S.totalWordRatio S.totalWordTranslation s) ^ (S.rhoMin ^ 2) := by
  dsimp only
  apply meanConditionalMapW_gap_affine_le_rpow
    ((S.ratioCrossingRule (r / s) (div_pos hr hs)).stoppedWordLaw S.alphabetLaw)
    ((S.ratioCrossingRule (r / s) (div_pos hr hs)).stoppedWordLaw_support_finite _)
    (T.stoppedWordLaw S.alphabetLaw) (T.stoppedWordLaw_support_finite _) S.totalWordRatio
    S.totalWordRatio S.totalWordTranslation S.totalWordTranslation hr hs (sq_nonneg _)
  · nlinarith [S.rhoMin_pos, S.rhoMin_lt_one]
  · intro x _
    exact S.totalWordRatio_ne_zero x
  · intro x hx
    exact ⟨(crossing_scale_window S hr hs hrs ⟨x, hx⟩).1,
      crossing_power_window S hr hs hrs ⟨x, hx⟩⟩

theorem single_block_W_le (S : System ι) (T : BoundedStoppingRule ι)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hrs : r ≤ s) :
    let G := S.ratioCrossingRule (r / s) (div_pos hr hs)
    meanConditionalMapW ((G.andThen T).stoppedWordLaw S.alphabetLaw)
      ((G.andThen T).stoppedWordLaw_support_finite _)
      S.totalWordRatio S.totalWordTranslation r ≤
      (meanConditionalMapW (T.stoppedWordLaw S.alphabetLaw) (T.stoppedWordLaw_support_finite _)
        S.totalWordRatio S.totalWordTranslation s) ^ (S.rhoMin ^ 2) := by
  dsimp only
  let G := S.ratioCrossingRule (r / s) (div_pos hr hs)
  let p := independentPair (G.stoppedWordLaw S.alphabetLaw) (T.stoppedWordLaw S.alphabetLaw)
  let hp : p.support.Finite := independentPair_support_finite _ _
    (G.stoppedWordLaw_support_finite _) (T.stoppedWordLaw_support_finite _)
  have he := finiteFunctional_congr
    (fun q hq ↦ meanConditionalMapW q hq S.totalWordRatio S.totalWordTranslation r)
    (G.andThen_stoppedWordLaw T S.alphabetLaw)
    ((G.andThen T).stoppedWordLaw_support_finite _)
    (by simpa using hp.image (fun z ↦ Word.concatenate z.1 z.2))
  rw [he, meanConditionalMapW_map _ hp]
  simp only [S.totalWordRatio_concatenate, S.totalWordTranslation_concatenate]
  exact (meanConditionalMapW_coarsening_le p hp (headLabel S)
    (fun b ↦ S.totalWordRatio b.1 * b.2)
    (fun z ↦ S.totalWordTranslation z.1 + S.totalWordRatio z.1 * S.totalWordTranslation z.2)
    hr.le).trans (crossing_head_W_le S T hr hs hrs)

theorem head_step_W_le (S : System ι) (T V : BoundedStoppingRule ι)
    {r s cap : ℝ} (hr : 0 < r) (hs : 0 < s) (hrs : r ≤ s) (hcap0 : 0 ≤ cap)
    (A : (headLabelLaw S (S.ratioCrossingRule (r / s) (div_pos hr hs)) T).support →
      BoundedStoppingRule ι)
    (hA : ∀ b, meanConditionalMapW (((A b).andThen V).stoppedWordLaw S.alphabetLaw)
      (((A b).andThen V).stoppedWordLaw_support_finite _) S.totalWordRatio S.totalWordTranslation
      (r / (|S.totalWordRatio b.val.1| * |b.val.2|)) ≤ cap) :
    let G := S.ratioCrossingRule (r / s) (div_pos hr hs)
    meanConditionalMapW (((headContinuation S G T A).andThen V).stoppedWordLaw S.alphabetLaw)
      (((headContinuation S G T A).andThen V).stoppedWordLaw_support_finite _)
      S.totalWordRatio S.totalWordTranslation r ≤
      cap * (meanConditionalMapW (T.stoppedWordLaw S.alphabetLaw) (T.stoppedWordLaw_support_finite _)
        S.totalWordRatio S.totalWordTranslation s) ^ (S.rhoMin ^ 2) := by
  dsimp only
  let G := S.ratioCrossingRule (r / s) (div_pos hr hs)
  let p := independentPair (G.stoppedWordLaw S.alphabetLaw) (T.stoppedWordLaw S.alphabetLaw)
  let hp : p.support.Finite := independentPair_support_finite _ _
    (G.stoppedWordLaw_support_finite _) (T.stoppedWordLaw_support_finite _)
  let k (b : (Σ n : ℕ, Word ι n) × ℝ) :=
    ((supportedRule (headLabelLaw S G T) A b).andThen V).stoppedWordLaw S.alphabetLaw
  let hk (b : (Σ n : ℕ, Word ι n) × ℝ) : (k b).support.Finite :=
    ((supportedRule (headLabelLaw S G T) A b).andThen V).stoppedWordLaw_support_finite _
  let coef (b : (Σ n : ℕ, Word ι n) × ℝ) := S.totalWordRatio b.1 * b.2
  let J := jointMixture p (fun z ↦ k (headLabel S z))
  let hJ : J.support.Finite := jointMixture_support_finite_of_finite p hp _
    (fun z ↦ hk (headLabel S z))
  have hcoef (z : (Σ n : ℕ, Word ι n) × (Σ n : ℕ, Word ι n)) (_hz : z ∈ p.support) :
      coef (headLabel S z) ≠ 0 :=
    mul_ne_zero (S.totalWordRatio_ne_zero z.1) (S.totalWordRatio_ne_zero z.2)
  have hcap (z : (Σ n : ℕ, Word ι n) × (Σ n : ℕ, Word ι n)) (hz : z ∈ p.support) :
      meanConditionalMapW (k (headLabel S z)) (hk (headLabel S z))
        S.totalWordRatio S.totalWordTranslation (r / |coef (headLabel S z)|) ≤ cap := by
    have hb : headLabel S z ∈ (headLabelLaw S G T).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨z, hz, rfl⟩
    let b : (headLabelLaw S G T).support := ⟨headLabel S z, hb⟩
    have he := supportedRule_at (headLabelLaw S G T) A b
    change supportedRule (headLabelLaw S G T) A (headLabel S z) = A b at he
    have h := hA b
    simpa only [k, hk, coef, he, abs_mul] using h
  have hbound := meanConditionalMapW_dependent_affine_coarsened_cap p hp (headLabel S) coef
    k hk S.totalWordRatio (fun z ↦ coef z.1 * z.2)
    (fun z ↦ S.totalWordTranslation z.1 + S.totalWordRatio z.1 * S.totalWordTranslation z.2)
    S.totalWordTranslation hr hcoef hcap
  have he := finiteFunctional_congr
    (fun q hq ↦ meanConditionalMapW q hq S.totalWordRatio S.totalWordTranslation r)
    (headContinuation_andThen_law S G T V A)
    (((headContinuation S G T A).andThen V).stoppedWordLaw_support_finite _)
    (by simpa using hJ.image (fun z ↦ Word.concatenate (Word.concatenate z.1.1 z.1.2) z.2))
  rw [he, meanConditionalMapW_map _ hJ]
  simp only [S.totalWordRatio_concatenate, S.totalWordTranslation_concatenate]
  exact hbound.trans (mul_le_mul_of_nonneg_left (crossing_head_W_le S T hr hs hrs) hcap0)

end ExactOverlaps.ConditionalW
