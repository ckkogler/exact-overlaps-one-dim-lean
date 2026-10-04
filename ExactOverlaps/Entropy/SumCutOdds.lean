module

public import ExactOverlaps.Entropy.SumCutPrediction
public import ExactOverlaps.Probability.CutOdds
public import ExactOverlaps.Probability.NonnegativeExpectations

/-!
# A measurable odds majorant for independent-sum cut entropy

At each positive atom the two sides of its cut location are written in
positive displacement coordinates. This prepares the direct nonnegative
integral argument, with all endpoint exclusions explicit.
-/

@[expose] public section

open MeasureTheory Set
open scoped Classical
open ExactOverlaps.FiniteProbability

namespace ExactOverlaps.Entropy

noncomputable def sumCutOddsLoss {α β : Type*} (p : PMF α) (q : PMF β)
    (hp : p.support.Finite) (hq : q.support.Finite) (x : α → ℝ) (y : β → ℝ)
    (a : ℝ) (z : α × β) : ℝ :=
  if x z.1 ≤ a then
    forwardCutOdds p hp x (a - x z.1) z.1 * backwardCutOdds q hq y (a - x z.1) z.2
  else backwardCutOdds p hp x (x z.1 - a) z.1 * forwardCutOdds q hq y (x z.1 - a) z.2

lemma sumCutOddsLoss_nonneg {α β : Type*} (p : PMF α) (q : PMF β)
    (hp : p.support.Finite) (hq : q.support.Finite) (x : α → ℝ) (y : β → ℝ)
    (a : ℝ) (z : α × β) : 0 ≤ sumCutOddsLoss p q hp hq x y a z := by
  unfold sumCutOddsLoss forwardCutOdds backwardCutOdds
  split_ifs <;> positivity

lemma measurable_sumCutOddsLoss {α β : Type*} (p : PMF α) (q : PMF β)
    (hp : p.support.Finite) (hq : q.support.Finite) (x : α → ℝ) (y : β → ℝ)
    (z : α × β) : Measurable (fun a ↦ sumCutOddsLoss p q hp hq x y a z) := by
  apply Measurable.ite (measurableSet_le measurable_const measurable_id)
  · exact ((measurable_forwardCutOdds p hp x z.1).comp (measurable_id.sub measurable_const)).mul
      ((measurable_backwardCutOdds q hq y z.2).comp (measurable_id.sub measurable_const))
  · exact ((measurable_backwardCutOdds p hp x z.1).comp (measurable_const.sub measurable_id)).mul
      ((measurable_forwardCutOdds q hq y z.2).comp (measurable_const.sub measurable_id))

lemma sumCutOddsLoss_right {α β : Type*} (p : PMF α) (q : PMF β)
    (hp : p.support.Finite) (hq : q.support.Finite) (x : α → ℝ) (y : β → ℝ)
    (z : α × β) {u : ℝ} (hu : 0 < u) :
    sumCutOddsLoss p q hp hq x y (x z.1 + u) z =
      forwardCutOdds p hp x u z.1 * backwardCutOdds q hq y u z.2 := by
  simp [sumCutOddsLoss, show x z.1 ≤ x z.1 + u by linarith]

lemma sumCutOddsLoss_left {α β : Type*} (p : PMF α) (q : PMF β)
    (hp : p.support.Finite) (hq : q.support.Finite) (x : α → ℝ) (y : β → ℝ)
    (z : α × β) {u : ℝ} (hu : 0 < u) :
    sumCutOddsLoss p q hp hq x y (x z.1 - u) z =
      backwardCutOdds p hp x u z.1 * forwardCutOdds q hq y u z.2 := by
  simp [sumCutOddsLoss, show ¬x z.1 ≤ x z.1 - u by linarith]

theorem conditional_sum_cut_entropy_le_odds {α β : Type*} (p : PMF α) (q : PMF β)
    (hp : p.support.Finite) (hq : q.support.Finite) (x : α → ℝ) (y : β → ℝ)
    (a : ℝ) (ha : ∀ u ∈ p.support, x u ≠ a) :
    conditionalCutEntropy (independentPair p q) (independentPair_support_finite p q hp hq)
      (fun z ↦ x z.1 + y z.2) (fun z ↦ x z.1) a ≤
      expectation (independentPair p q) (independentPair_support_finite p q hp hq)
        (sumCutOddsLoss p q hp hq x y a) := by
  apply (conditional_sum_cut_entropy_le_loss p q hp hq x y a ha).trans
  apply expectation_mono
  intro z hz
  rw [independentPair_support] at hz
  by_cases hxa : x z.1 ≤ a
  · have hlt : x z.1 < a := lt_of_le_of_ne hxa (ha z.1 hz.1)
    have h := productPredictor_true_loss_le
      ⟨cumulativeMass_pos_of_atom_le p hp x z.1 hz.1 hxa, cumulativeMass_le_one p hp x a⟩
      ⟨cumulativeMass_nonneg q hq y (x z.1 + y z.2 - a),
        cumulativeMass_lt_one_of_lt_atom q hq y z.2 hz.2 (by linarith)⟩
    have hx : x z.1 + (a - x z.1) = a := by ring
    have hy : y z.2 - (a - x z.1) = x z.1 + y z.2 - a := by ring
    simpa only [hxa, ite_true, sumCutOddsLoss, sumCutPredictor,
      forwardCutOdds, backwardCutOdds, hx, hy] using h
  · have hlt : a < x z.1 := lt_of_not_ge hxa
    have h := productPredictor_false_loss_le
      ⟨cumulativeMass_nonneg p hp x a, cumulativeMass_lt_one_of_lt_atom p hp x z.1 hz.1 hlt⟩
      ⟨cumulativeMass_pos_of_atom_le q hq y z.2 hz.2 (by linarith),
        cumulativeMass_le_one q hq y (x z.1 + y z.2 - a)⟩
    have hx : x z.1 - (x z.1 - a) = a := by ring
    have hy : y z.2 + (x z.1 - a) = x z.1 + y z.2 - a := by ring
    simpa only [hxa, ite_false, sumCutOddsLoss, sumCutPredictor,
      forwardCutOdds, backwardCutOdds, hx, hy] using h

end ExactOverlaps.Entropy
