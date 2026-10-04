module

public import ExactOverlaps.MainTheorem.StoppedScales
public import ExactOverlaps.MainTheorem.GeometricCost
public import ExactOverlaps.StoppedConcatenation.WordScalars
public import ExactOverlaps.StoppedConcatenation.ConditionalPushforward

/-!
Reversing the selected blocks supplies all-pairs separation and a genuine
geometric bound for products of their conditional W values.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace ExactOverlaps.MainTheorem

open SelfSimilar StoppedConcatenation ConvolutionDisintegration

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem reversed_stopped_separation_all (S : System ι)
    (T : ℕ → BoundedStoppingRule ι) (r : ℕ → ℝ) (hr : StrictAnti r)
    (hsep : ∀ n, ∀ w ∈ ((T (n + 1)).stoppedWordLaw S.alphabetLaw).support,
      r (n + 1) < S.rhoMin * r n * |S.wordRatio w.1 w.2|)
    (n : ℕ) (i j : Fin (n + 1)) (hij : i < j)
    (w : Σ k : ℕ, Word ι k)
    (hw : w ∈ ((T (n - i)).stoppedWordLaw S.alphabetLaw).support) :
    r (n - i) ≤ S.rhoMin * r (n - j) * |S.totalWordRatio w| := by
  have hi : (i : ℕ) < n := by have := j.isLt; omega
  have h := reversed_stopped_separation S T r hsep n ⟨i, hi⟩ w hw
  have hidx : n - j ≤ n - ((i : ℕ) + 1) := by omega
  have hscale := hr.antitone hidx
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hscale S.rhoMin_pos.le) (abs_nonneg _))

theorem reversed_conditional_product_le (S : System ι)
    (T : ℕ → BoundedStoppingRule ι) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    {κ : ℝ} (hκ : 0 < κ)
    (hcap : ∀ n, meanConditionalMapW ((T n).stoppedWordLaw S.alphabetLaw)
      ((T n).stoppedWordLaw_support_finite S.alphabetLaw)
      S.totalWordRatio S.totalWordTranslation (r n) ≤ Real.exp (-κ)) (n : ℕ) :
    (∏ j : Fin (n + 1), (meanConditionalMapW ((T (n - j)).stoppedWordLaw S.alphabetLaw)
      ((T (n - j)).stoppedWordLaw_support_finite S.alphabetLaw)
      S.totalWordRatio S.totalWordTranslation (r (n - j))) ^ (S.rhoMin ^ 2)) ≤
      Real.exp (-((n : ℝ) * κ * S.rhoMin ^ 2)) := by
  have h := product_rpow_le_exp
    (fun j : Fin (n + 1) ↦ meanConditionalMapW ((T (n - j)).stoppedWordLaw S.alphabetLaw)
      ((T (n - j)).stoppedWordLaw_support_finite S.alphabetLaw)
      S.totalWordRatio S.totalWordTranslation (r (n - j))) κ (S.rhoMin ^ 2)
    (sq_nonneg _) (fun j ↦ meanConditionalMapW_nonneg _ _ _ _ (hr (n - j)).le)
    (fun j ↦ hcap (n - j))
  apply h.trans
  apply Real.exp_le_exp.mpr
  push_cast
  nlinarith [sq_nonneg S.rhoMin]

end ExactOverlaps.MainTheorem
