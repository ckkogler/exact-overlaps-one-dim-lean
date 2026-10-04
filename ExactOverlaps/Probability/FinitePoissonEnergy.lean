module

public import ExactOverlaps.Probability.OrderedFinitePresentation
public import ExactOverlaps.Probability.OrderedPoissonEnergy

/-!
# Poisson dispersion comparison for an arbitrary finite real law

Only cuts between consecutive support points affect the cell label of a
finite law. Each such gap is cut independently with probability
`1 - exp (-t * gap)`. The definitions below average actual conditional laws
over that finite partition distribution, including the partition itself in
the observation. The sorted support presentation maps exactly to the law.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ExactOverlaps.Poisson

noncomputable def finitePoissonDispersion (p : PMF ℝ) (hp : p.support.Finite)
    (t : ℝ) : ℝ :=
  let P := orderedFinitePresentation p hp
  cutDispersion P.law (Set.toFinite _) P.coordinate t

noncomputable def finitePoissonVariance (p : PMF ℝ) (hp : p.support.Finite)
    (t : ℝ) : ℝ :=
  let P := orderedFinitePresentation p hp
  cutVariance P.law (Set.toFinite _) P.coordinate t

lemma orderedPresentation_monotoneOn {p : PMF ℝ} (P : OrderedFinitePresentation p) :
    MonotoneOn P.coordinate (Icc 0 P.size) := by
  intro a ha b hb hab
  exact P.strictlyOrdered.monotone
    (show (⟨a, Nat.lt_succ_iff.mpr ha.2⟩ : Fin (P.size + 1)) ≤
      ⟨b, Nat.lt_succ_iff.mpr hb.2⟩ from hab)

theorem finitePoissonDispersion_le_integratedVariance (p : PMF ℝ) (hp : p.support.Finite) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (finitePoissonDispersion p hp t)) ≤
      2 * ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t * finitePoissonVariance p hp t) := by
  let P := orderedFinitePresentation p hp
  exact lintegral_cutDispersion_le P.law (Set.toFinite _) P.coordinate
    (orderedPresentation_monotoneOn P)

theorem finitePoissonVariance_energy_identity (p : PMF ℝ) (hp : p.support.Finite) :
    2 * (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t * finitePoissonVariance p hp t)) =
      3 * VarianceEnergy.energy p.toMeasure := by
  let P := orderedFinitePresentation p hp
  have h := two_lintegral_time_cutVariance_eq_three_energy P.law (Set.toFinite _)
    P.coordinate P.strictlyOrdered
  rw [P.map_eq] at h
  exact h

/-- The finite-law Poisson dispersion inequality, with the paper's constant three. -/
theorem finitePoissonDispersion_le_three_energy (p : PMF ℝ) (hp : p.support.Finite) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (finitePoissonDispersion p hp t)) ≤
      3 * VarianceEnergy.energy p.toMeasure := by
  exact (finitePoissonDispersion_le_integratedVariance p hp).trans_eq
    (finitePoissonVariance_energy_identity p hp)

end ExactOverlaps.Poisson
