module

public import ExactOverlaps.SelfSimilar.MoranSystem
public import ExactOverlaps.SelfSimilar.AttractorHausdorff

/-!
The full attractor-dimension conclusion follows from the measure-dimension
formula. This intermediate theorem states that formula as an explicit
premise; its unconditional discharge belongs to the main theorem assembly.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι]

theorem dimH_attractor_eq_of_measure_dimension_formula (S : System ι)
    (hformula : ∀ (T : System ι) (μ : ProbabilityMeasure ℝ),
      T.IsStationary (μ : Measure ℝ) →
      (lowerHausdorffDimension (μ : Measure ℝ)).toReal =
        min 1 (T.randomWalkEntropyRate / |T.lyapunov|))
    {s : ℝ} (hs : 0 ≤ s) (hpressure : S.pressure s = 1)
    (hS : S.HasNoExactOverlaps) : dimH S.attractor = ENNReal.ofReal (min 1 s) := by
  apply le_antisymm (S.dimH_attractor_le_min hs hpressure)
  let : MeasurableSpace ι := ⊤
  let T := S.moranSystem s hpressure
  let μ := T.codingMeasure.toProbabilityMeasure
  have hμ : T.IsStationary (μ : Measure ℝ) := T.codingMeasure_isStationary
  have hd := hformula T μ hμ
  have hratio : T.randomWalkEntropyRate / |T.lyapunov| = s :=
    S.moranSystem_entropyRate_div_lyapunov hpressure hS
  rw [hratio] at hd
  have he : ENNReal.ofReal (min 1 s) = lowerHausdorffDimension (μ : Measure ℝ) := by
    rw [← hd, ENNReal.ofReal_toReal (lowerHausdorffDimension_ne_top (μ : Measure ℝ))]
  rw [he]
  have h := T.dimension_le_attractor μ hμ
  simpa only [T, S.moranSystem_attractor hpressure] using h

theorem corollary_1_2_of_measure_dimension_formula (S : System ι)
    (hformula : ∀ (T : System ι) (μ : ProbabilityMeasure ℝ),
      T.IsStationary (μ : Measure ℝ) →
      (lowerHausdorffDimension (μ : Measure ℝ)).toReal =
        min 1 (T.randomWalkEntropyRate / |T.lyapunov|))
    {s : ℝ} (hs : 0 ≤ s) (hpressure : S.pressure s = 1)
    (hS : S.HasNoExactOverlaps) {K : Set ℝ}
    (hK : IsCompact K) (hKn : K.Nonempty) (hKi : K = ⋃ i, (S.map i) '' K) :
    dimH K = ENNReal.ofReal (min 1 s) := by
  rw [S.eq_attractor_of_compact_invariant hK hKn hKi]
  exact S.dimH_attractor_eq_of_measure_dimension_formula hformula hs hpressure hS

end ExactOverlaps.SelfSimilar.System
