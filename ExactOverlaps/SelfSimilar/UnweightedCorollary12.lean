module

public import ExactOverlaps.SelfSimilar.Corollary12Conditional
public import ExactOverlaps.SelfSimilar.UnweightedAttractor

/-!
The corollary's interface for an unweighted finite family. Its no-overlap
condition is freeness of actual affine word composition and does not refer
to probability weights or a coding construction.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ExactOverlaps.SelfSimilar

/-- Ordered composition of an unweighted finite word. -/
noncomputable def composeWord {ι : Type*} (g : ι → RealSimilarity) :
    (n : ℕ) → Word ι n → RealSimilarity
  | 0, _ => RealSimilarity.identity
  | n + 1, w => (g w.1).comp (composeWord g n w.2)

/-- Distinct finite words give distinct actual similarities. -/
def HasNoExactOverlaps {ι : Type*} (g : ι → RealSimilarity) : Prop :=
  Function.Injective (fun w : Σ n : ℕ, Word ι n ↦ composeWord g w.1 w.2)

variable {ι : Type*} [Fintype ι]

theorem System.wordMap_eq_composeWord (S : System ι) (n : ℕ) (w : Word ι n) :
    S.wordMap n w = composeWord S.map n w := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (S.map w.1).comp (S.wordMap n w.2) = (S.map w.1).comp (composeWord S.map n w.2)
    rw [ih]

theorem System.noExactOverlaps_of_family (S : System ι) (h : SelfSimilar.HasNoExactOverlaps S.map) :
    S.HasNoExactOverlaps := by
  intro v w he
  apply h
  simpa only [S.wordMap_eq_composeWord] using he

theorem corollary_1_2_of_measure_dimension_formula [Nonempty ι]
    (g : ι → RealSimilarity) (hg : ∀ i, |(g i).ratio| < 1)
    (hformula : ∀ (T : System ι) (μ : ProbabilityMeasure ℝ),
      T.IsStationary (μ : Measure ℝ) →
      (lowerHausdorffDimension (μ : Measure ℝ)).toReal =
        min 1 (T.randomWalkEntropyRate / |T.lyapunov|))
    {s : ℝ} (hs : 0 ≤ s) (hpressure : (∑ i, |(g i).ratio| ^ s) = 1)
    (hfree : HasNoExactOverlaps g) {K : Set ℝ}
    (hK : IsCompact K) (hKn : K.Nonempty) (hKi : K = ⋃ i, (g i) '' K) :
    dimH K = ENNReal.ofReal (min 1 s) := by
  let S := uniformSystem g hg
  exact S.corollary_1_2_of_measure_dimension_formula hformula hs hpressure
    (S.noExactOverlaps_of_family hfree) hK hKn hKi

end ExactOverlaps.SelfSimilar
