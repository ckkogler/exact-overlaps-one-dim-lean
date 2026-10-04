module

public import ExactOverlaps.EntropyEnergyGap.ScaleAverage
public import ExactOverlaps.EntropyEnergyGap.DigitCopies

/-!
# Variance energy from the entropy gap of a finite digit array

This is Proposition 3.3 for actual finite digit-vector laws, with arbitrary
real values and coefficients and the exact source constants. The argument
allows dependence among the positions of one vector; independent copies
and their conditional product laws are constructed in the proof chain.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators Classical
open ExactOverlaps.Entropy ExactOverlaps.VarianceEnergy

namespace ExactOverlaps.EntropyEnergyGap

noncomputable def finiteLawProbability (p : PMF ℝ) : ProbabilityMeasure ℝ :=
  ⟨p.toMeasure, inferInstance⟩

lemma finiteLawProbability_bounded (p : PMF ℝ) (hp : p.support.Finite) :
    HasBoundedSupport (finiteLawProbability p) := by
  obtain ⟨b, D, h⟩ := exists_support_interval p.toMeasure hp.toFinset (finiteLaw_ae_mem_support p hp)
  exact ⟨b, b + D, h⟩

lemma digitValueSum_support_finite {α ι : Type*} [Fintype α] [Fintype ι]
    (v : ι → α → ℝ) (a : ι → ℝ) (ν : PMF (ι → α)) :
    (ν.map (digitValueSum v a)).support.Finite := by
  simpa using (Set.toFinite ν.support).image (digitValueSum v a)

/-- Proposition 3.3 for an actual law of a finite digit array. -/
theorem digit_array_energy_gap {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι]
    (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ)
    (v : ι → α → ℝ) (a : ι → ℝ) (a₀ : α) (ν : PMF (ι → α))
    (hLaw : (μ : Measure ℝ) = (ν.map (digitValueSum v a)).toMeasure)
    (m : ℕ) (hm : 0 < m) {R : ℝ} (hR : 0 < R) :
    1 / (30 * m) *
        (finiteEntropy (ν.map (digitValueSum v a)) (digitValueSum_support_finite v a ν) -
          ScaleEntropy.entropy μ hμ R hR -
          (Fintype.card ι : ℝ) * (Fintype.card α - 1 : ℕ) * Real.log (m + 1 : ℝ) / m) - 1 / 2 ≤
      (energyBelow (μ : Measure ℝ) R).toReal := by
  rw [hLaw]
  exact energyBelow_ge_entropy_gap μ hμ (ν.map (digitValueSum v a))
    (digitValueSum_support_finite v a ν) hLaw m hm
    ((Fintype.card ι : ℝ) * (Fintype.card α - 1 : ℕ) * Real.log (m + 1 : ℝ))
    (copied_digit_sum_entropy_le v a a₀ ν m (digitValueSum_support_finite v a ν)) hR

/-- The same digit-array theorem with its bounded probability law constructed automatically. -/
theorem digit_array_energy_gap_pmf {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι]
    (v : ι → α → ℝ) (a : ι → ℝ) (a₀ : α) (ν : PMF (ι → α))
    (m : ℕ) (hm : 0 < m) {R : ℝ} (hR : 0 < R) :
    1 / (30 * m) *
        (finiteEntropy (ν.map (digitValueSum v a)) (digitValueSum_support_finite v a ν) -
          ScaleEntropy.entropy (finiteLawProbability (ν.map (digitValueSum v a)))
            (finiteLawProbability_bounded _ (digitValueSum_support_finite v a ν)) R hR -
          (Fintype.card ι : ℝ) * (Fintype.card α - 1 : ℕ) * Real.log (m + 1 : ℝ) / m) - 1 / 2 ≤
      (energyBelow (ν.map (digitValueSum v a)).toMeasure R).toReal := by
  exact digit_array_energy_gap (finiteLawProbability (ν.map (digitValueSum v a)))
    (finiteLawProbability_bounded _ (digitValueSum_support_finite v a ν)) v a a₀ ν rfl m hm hR

end ExactOverlaps.EntropyEnergyGap
