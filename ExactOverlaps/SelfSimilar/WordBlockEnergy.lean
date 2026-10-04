module

public import ExactOverlaps.SelfSimilar.ConditionalDigitEnergy
public import ExactOverlaps.SelfSimilar.BoundedBlockGeometry
public import ExactOverlaps.SelfSimilar.BlockRatioEntropy

/-! The deterministic block entropy-gap bound for the actual random walk. -/

@[expose] public section

open MeasureTheory
open scoped BigOperators Classical

namespace ExactOverlaps.SelfSimilar.System

open Entropy EntropyEnergyGap
variable {ι : Type*} [Fintype ι]

noncomputable def blockEntropyPenalty (_S : System ι) (N m : ℕ) : ℝ :=
  (Fintype.card ι : ℝ) * Real.log (N + 1 : ℝ) +
    (Fintype.card (BoundedWord ι N) - 1 : ℕ) * Real.log (m + 1 : ℝ) / m

theorem finiteLawProbability_wordTranslationLaw (S : System ι) (n : ℕ) :
    finiteLawProbability (S.wordTranslationLaw n) = S.wordTranslationProbability n := by
  apply ProbabilityMeasure.toMeasure_injective
  rfl

theorem word_block_energy_bound (S : System ι) {N r : ℕ} (hr : r ≤ N)
    (L m : ℕ) (hm : 0 < m) {R : ℝ} (hR : 0 < R) :
    1 / (30 * m) *
      (finiteEntropy (S.wordTranslationLaw (blockLength N r L))
          (S.wordTranslationLaw_support_finite (blockLength N r L)) -
        ScaleEntropy.entropy (S.wordTranslationProbability (blockLength N r L))
          (S.wordTranslationProbability_hasBoundedSupport (blockLength N r L)) R hR -
        (L + 1 : ℝ) * S.blockEntropyPenalty N m) - 1 / 2 ≤
      S.meanRatioTranslationEnergy (blockLength N r L) R := by
  let n := blockLength N r L
  let e := boundedBlockEncode (ι := ι) hr L
  let f : Word ι n → Fin (L + 1) → ℝ := fun w j ↦ S.boundedWordRatio N (e w j)
  let a : (Fin (L + 1) → ℝ) → Fin (L + 1) → ℝ := prefixCoefficient (L + 1)
  have hg := mean_conditional_digit_energy_gap (S.wordLaw n) (Set.toFinite _) f (S.wordTranslation n)
    e (fun _ ↦ S.boundedWordTranslation N) a (BoundedWord.empty N)
    (fun w _ ↦ S.wordTranslation_eq_block_digitSum hr L w) m hm hR
  have hT := S.blockRatioVector_entropy_le N (L + 1) ((S.wordLaw n).map e)
  have hmap : ((S.wordLaw n).map e).map (fun x j ↦ S.boundedWordRatio N (x j)) =
      (S.wordLaw n).map f := by rw [PMF.map_comp]; rfl
  simp only [hmap, Nat.cast_add, Nat.cast_one] at hT
  have href := meanConditionalMapEnergy_refinement_le (S.wordLaw n) (Set.toFinite _) f
    (fun t : Fin (L + 1) → ℝ ↦ ∏ j, t j) (S.wordTranslation n) R
  have hRfun : (fun w : Word ι n ↦ ∏ j, f w j) = S.wordRatio n := by
    funext w
    exact (S.wordRatio_eq_block_product hr L w).symm
  rw [hRfun] at href
  change _ ≤ S.meanRatioTranslationEnergy n R at href
  apply le_trans _ (hg.trans href)
  apply sub_le_sub_right
  apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ) ≤ 1 / (30 * m))
  have hprob := S.finiteLawProbability_wordTranslationLaw n
  change finiteEntropy (S.wordTranslationLaw n) _ -
      ScaleEntropy.entropy (S.wordTranslationProbability n) _ R hR -
      (L + 1 : ℝ) * S.blockEntropyPenalty N m ≤
    finiteEntropy (S.wordTranslationLaw n) _ - finiteEntropy ((S.wordLaw n).map f) _ -
      ScaleEntropy.entropy (finiteLawProbability (S.wordTranslationLaw n)) _ R hR -
      (Fintype.card (Fin (L + 1)) : ℝ) *
        (Fintype.card (BoundedWord ι N) - 1 : ℕ) * Real.log (m + 1 : ℝ) / m
  simp only [hprob, Fintype.card_fin, Nat.cast_add, Nat.cast_one, blockEntropyPenalty]
  ring_nf at hT ⊢
  linarith only [hT]

theorem word_block_energy_bound_all (S : System ι) {N : ℕ} (hN : 0 < N)
    (n m : ℕ) (hm : 0 < m) {R : ℝ} (hR : 0 < R) :
    1 / (30 * m) *
      (finiteEntropy (S.wordTranslationLaw n) (S.wordTranslationLaw_support_finite n) -
        ScaleEntropy.entropy (S.wordTranslationProbability n)
          (S.wordTranslationProbability_hasBoundedSupport n) R hR -
        ((n / N : ℕ) + 1 : ℝ) * S.blockEntropyPenalty N m) - 1 / 2 ≤
      S.meanRatioTranslationEnergy n R := by
  have he : blockLength N (n % N) (n / N) = n := by
    rw [blockLength_eq]
    exact Nat.mod_add_div n N
  simpa only [he] using
    S.word_block_energy_bound (Nat.mod_lt n hN).le (n / N) m hm hR

end ExactOverlaps.SelfSimilar.System
