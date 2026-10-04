module

public import ExactOverlaps.Probability.OrderedCDFEstimate
public import ExactOverlaps.Probability.CDFTransport
public import ExactOverlaps.Probability.OrderedFinitePresentation

/-!
# Shifted distribution-function square-root estimate

The estimate holds for every finite real probability law. Increasing support
reindexing reduces it to the finite cumulative-weight bound, then exact PMF
transport identifies both the odds expectation and the independent tail.
-/

@[expose] public section

namespace ExactOverlaps.FiniteProbability

/-- The shifted cumulative-distribution estimate used in the cumulative-entropy bound. -/
theorem cdf_sqrt_odds_le (p : PMF ℝ) (hp : p.support.Finite) {r : ℝ} (hr : 0 ≤ r) :
    cdfOddsExpectation p hp (fun a ↦ a) r ≤
      3 * Real.sqrt (2 * distanceTail p hp (fun a ↦ a) r) := by
  let P := Poisson.orderedFinitePresentation p hp
  let hq : P.law.support.Finite := Set.toFinite _
  let x : Fin (P.size + 1) → ℝ := fun a ↦ P.coordinate a.val
  let hm : (P.law.map x).support.Finite := by simpa using hq.image x
  have h := expectation_shiftedCDF_sqrt_odds_le P.law hq P.coordinate P.strictlyOrdered.monotone hr
  change cdfOddsExpectation P.law hq x r ≤ 3 * Real.sqrt (2 * distanceTail P.law hq x r) at h
  have hleft : cdfOddsExpectation P.law hq x r = cdfOddsExpectation p hp (fun a ↦ a) r := by
    exact (cdfOddsExpectation_map P.law hq x (fun a ↦ a) r).symm.trans
      (cdfOddsExpectation_congr_law (P.law.map x) p hm hp P.map_eq (fun a ↦ a) r)
  have hright : distanceTail P.law hq x r = distanceTail p hp (fun a ↦ a) r := by
    exact (distanceTail_map P.law hq x (fun a ↦ a) r).symm.trans
      (distanceTail_congr_law (P.law.map x) p hm hp P.map_eq (fun a ↦ a) r)
  rw [hleft, hright] at h
  exact h

/-- The same bound for a real statistic on an arbitrary finite probability space. -/
theorem cdf_sqrt_odds_le_statistic {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (x : α → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    cdfOddsExpectation p hp x r ≤ 3 * Real.sqrt (2 * distanceTail p hp x r) := by
  have h := cdf_sqrt_odds_le (p.map x) (by simpa using hp.image x) hr
  rw [cdfOddsExpectation_map, distanceTail_map] at h
  exact h

end ExactOverlaps.FiniteProbability
