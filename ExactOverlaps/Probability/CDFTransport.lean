module

public import ExactOverlaps.Probability.IndexedQuantile
public import ExactOverlaps.Probability.FiniteDistanceTail

/-!
# Transport of finite cumulative masses and distance tails

The cumulative estimates depend only on the real law of the statistic.
These identities transfer them through exact maps of actual PMFs.
-/

@[expose] public section

namespace ExactOverlaps.FiniteProbability

noncomputable def cdfOddsExpectation {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (x : α → ℝ) (r : ℝ) : ℝ :=
  expectation p hp (fun a ↦ Real.sqrt
    ((1 - cumulativeMass p hp x (x a + r)) / cumulativeMass p hp x (x a + r)))

lemma cumulativeMass_map {α β : Type*} (p : PMF α) (hp : p.support.Finite)
    (f : α → β) (g : β → ℝ) (a : ℝ) :
    cumulativeMass (p.map f) (by simpa using hp.image f) g a =
      cumulativeMass p hp (fun z ↦ g (f z)) a := by
  exact expectation_map p hp f (fun b ↦ if g b ≤ a then 1 else 0)

lemma distanceTail_map {α β : Type*} (p : PMF α) (hp : p.support.Finite)
    (f : α → β) (g : β → ℝ) (r : ℝ) :
    distanceTail (p.map f) (by simpa using hp.image f) g r =
      distanceTail p hp (fun z ↦ g (f z)) r := by
  rw [distanceTail_eq_cumulative_complement, distanceTail_eq_cumulative_complement]
  simp_rw [cumulativeMass_map p hp f g]
  exact expectation_map p hp f _

lemma cdfOddsExpectation_map {α β : Type*} (p : PMF α) (hp : p.support.Finite)
    (f : α → β) (g : β → ℝ) (r : ℝ) :
    cdfOddsExpectation (p.map f) (by simpa using hp.image f) g r =
      cdfOddsExpectation p hp (fun z ↦ g (f z)) r := by
  unfold cdfOddsExpectation
  simp_rw [cumulativeMass_map p hp f g]
  exact expectation_map p hp f _

lemma distanceTail_congr_law {α : Type*} (p q : PMF α) (hp : p.support.Finite)
    (hq : q.support.Finite) (h : p = q) (x : α → ℝ) (r : ℝ) :
    distanceTail p hp x r = distanceTail q hq x r := by
  cases h
  rfl

lemma cdfOddsExpectation_congr_law {α : Type*} (p q : PMF α) (hp : p.support.Finite)
    (hq : q.support.Finite) (h : p = q) (x : α → ℝ) (r : ℝ) :
    cdfOddsExpectation p hp x r = cdfOddsExpectation q hq x r := by
  cases h
  rfl

end ExactOverlaps.FiniteProbability
