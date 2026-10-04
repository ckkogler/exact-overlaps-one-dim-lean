/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.MainTheorem.DecaySequence
public import ExactOverlaps.WImprovement.Proposition312
public import ExactOverlaps.SelfSimilar.DimensionEntropyUpperBound

/-!
Theorem 1.1: the standard Hausdorff dimension of a stationary probability
measure for a finite family of contracting real similarities equals the
minimum of one and the genuine random-walk entropy rate divided by the
absolute Lyapunov exponent. Signed contractions and zero listed weights
are allowed. No separation or dimension conclusion is assumed.
-/

@[expose] public section

open MeasureTheory

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι]

theorem theorem_1_1 (S : System ι) (μ : ProbabilityMeasure ℝ)
    (hμ : S.IsStationary (μ : Measure ℝ)) :
    (lowerHausdorffDimension (μ : Measure ℝ)).toReal =
      min 1 (S.randomWalkEntropyRate / |S.lyapunov|) := by
  let : MeasurableSpace ι := ⊤
  apply le_antisymm (S.dimension_le_min_entropyRate μ hμ)
  by_contra h
  have hdim : (lowerHausdorffDimension (μ : Measure ℝ)).toReal <
      min 1 (S.randomWalkEntropyRate / |S.lyapunov|) := lt_of_not_ge h
  obtain ⟨κ, hκ, havail⟩ := S.proposition_3_12 μ hμ hdim
  have hd := S.dimension_eq_one_of_improving_stops μ hμ hκ havail
  have hbad : (1 : ℝ) < min 1 (S.randomWalkEntropyRate / |S.lyapunov|) := by
    simpa only [hd, ENNReal.toReal_one] using hdim
  exact (not_lt_of_ge (min_le_left _ _)) hbad

/-- The same standard dimension formula without converting the dimension to a real number. -/
theorem theorem_1_1_ennreal (S : System ι) (μ : ProbabilityMeasure ℝ)
    (hμ : S.IsStationary (μ : Measure ℝ)) :
    lowerHausdorffDimension (μ : Measure ℝ) =
      ENNReal.ofReal (min 1 (S.randomWalkEntropyRate / |S.lyapunov|)) := by
  rw [← S.theorem_1_1 μ hμ, ENNReal.ofReal_toReal (lowerHausdorffDimension_ne_top _)]

end ExactOverlaps.SelfSimilar.System
