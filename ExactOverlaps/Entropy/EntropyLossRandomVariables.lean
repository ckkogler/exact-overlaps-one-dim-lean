module

public import ExactOverlaps.Entropy.EntropyLoss
public import ExactOverlaps.Probability.IndependentSumLaw

/-!
# Entropy loss for standard independent finite random variables

The probability space is arbitrary, and independence is Mathlib's
`iIndepFun`. The given finite marginal PMFs represent the actual marginal
laws exactly. The sum has a finite PMF law, and the inequality uses the
variance energies of the actual push-forward measures.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

namespace ExactOverlaps.Entropy

theorem independent_sum_support_finite {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : ℕ) (X : Fin m → Ω → ℝ)
    (hXm : ∀ i, AEMeasurable (X i) μ) (hXi : iIndepFun X μ)
    (p : Fin m → PMF ℝ) (hp : ∀ i, (p i).support.Finite)
    (hLaw : ∀ i, μ.map (X i) = (p i).toMeasure)
    (q : PMF ℝ) (hSumLaw : μ.map (fun ω ↦ ∑ i, X i ω) = q.toMeasure) :
    q.support.Finite := by
  have hq : q = (tupleLaw m p).map (tupleSum id m) :=
    PMF.toMeasure_injective (hSumLaw.symm.trans (independent_sum_law μ m X hXm hXi p hp hLaw))
  rw [hq]
  simpa using (tupleLaw_support_finite m p hp).image (tupleSum id m)

/-- Theorem 1.3 with standard independence and the actual marginal and sum laws. -/
theorem independent_finite_entropy_loss {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : ℕ) (X : Fin m → Ω → ℝ)
    (hXm : ∀ i, AEMeasurable (X i) μ) (hXi : iIndepFun X μ)
    (p : Fin m → PMF ℝ) (hp : ∀ i, (p i).support.Finite)
    (hLaw : ∀ i, μ.map (X i) = (p i).toMeasure)
    (q : PMF ℝ) (hq : q.support.Finite)
    (hSumLaw : μ.map (fun ω ↦ ∑ i, X i ω) = q.toMeasure) :
    (∑ i, finiteEntropy (p i) (hp i)) - finiteEntropy q hq ≤
      30 * m * ∑ i, (VarianceEnergy.energy (μ.map (X i))).toReal := by
  have he : q = (tupleLaw m p).map (tupleSum id m) :=
    PMF.toMeasure_injective (hSumLaw.symm.trans (independent_sum_law μ m X hXm hXi p hp hLaw))
  have h := entropy_loss_le_thirty m p hp
  have hH := ExactOverlaps.FiniteProbability.finiteFunctional_congr
    (fun r hr ↦ finiteEntropy r hr) he hq
    (by simpa using (tupleLaw_support_finite m p hp).image (tupleSum id m))
  rw [hH]
  simpa only [hLaw] using h

/-- The sum law and its finiteness are conclusions, not extra assumptions. -/
theorem independent_finite_entropy_loss_exists {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : ℕ) (X : Fin m → Ω → ℝ)
    (hXm : ∀ i, AEMeasurable (X i) μ) (hXi : iIndepFun X μ)
    (p : Fin m → PMF ℝ) (hp : ∀ i, (p i).support.Finite)
    (hLaw : ∀ i, μ.map (X i) = (p i).toMeasure) :
    ∃ (q : PMF ℝ) (hq : q.support.Finite),
      μ.map (fun ω ↦ ∑ i, X i ω) = q.toMeasure ∧
      (∑ i, finiteEntropy (p i) (hp i)) - finiteEntropy q hq ≤
        30 * m * ∑ i, (VarianceEnergy.energy (μ.map (X i))).toReal := by
  let q := (tupleLaw m p).map (tupleSum id m)
  have hq : q.support.Finite := by
    simpa [q] using (tupleLaw_support_finite m p hp).image (tupleSum id m)
  have hSumLaw := independent_sum_law μ m X hXm hXi p hp hLaw
  exact ⟨q, hq, hSumLaw, independent_finite_entropy_loss μ m X hXm hXi p hp hLaw q hq hSumLaw⟩

end ExactOverlaps.Entropy
