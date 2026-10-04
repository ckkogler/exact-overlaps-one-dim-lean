module

public import ExactOverlaps.Entropy.SumCutOdds
public import ExactOverlaps.Probability.CutOddsIntegral
public import ExactOverlaps.Probability.FiniteCutIntegration

/-!
# Cumulative conditional entropy of an independent sum

For independent finite real statistics, integrating the actual entropy of a
cut of the first statistic conditional on their sum is bounded by nine times
the sum of the two dispersions. Nonnegative integration proves finiteness
first; the ordinary real integral statement is then justified explicitly.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal Classical
open ExactOverlaps.FiniteProbability

namespace ExactOverlaps.Entropy

lemma ae_cut_not_support_atom {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (x : α → ℝ) : ∀ᵐ a : ℝ, ∀ z ∈ p.support, x z ≠ a := by
  apply (ae_ball_iff hp.countable).mpr
  intro z _
  filter_upwards [(Set.countable_singleton (x z)).ae_notMem volume] with a ha
  simpa only [Set.mem_singleton_iff, ne_comm] using ha

theorem lintegral_sumCutOddsLoss_le {α β : Type*} (p : PMF α) (q : PMF β)
    (hp : p.support.Finite) (hq : q.support.Finite) (x : α → ℝ) (y : β → ℝ) :
    (∫⁻ a, ENNReal.ofReal
      (expectation (independentPair p q) (independentPair_support_finite p q hp hq)
        (sumCutOddsLoss p q hp hq x y a))) ≤
      ENNReal.ofReal (9 * (FiniteLaw.dispersion p hp x + FiniteLaw.dispersion q hq y)) := by
  rw [lintegral_expectation_translated_halflines (independentPair p q)
    (independentPair_support_finite p q hp hq) (fun z ↦ x z.1)
    (sumCutOddsLoss p q hp hq x y)
    (fun z _ ↦ measurable_sumCutOddsLoss p q hp hq x y z)
    (fun z _ a ↦ sumCutOddsLoss_nonneg p q hp hq x y a z)]
  have hl : (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal
      (expectation (independentPair p q) (independentPair_support_finite p q hp hq)
        (fun z ↦ sumCutOddsLoss p q hp hq x y (x z.1 - u) z))) =
      ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal
      (expectation (independentPair p q) (independentPair_support_finite p q hp hq)
        (fun z ↦ backwardCutOdds p hp x u z.1 * forwardCutOdds q hq y u z.2)) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    congr 1
    apply expectation_congr
    intro z _
    exact sumCutOddsLoss_left p q hp hq x y z hu
  have hr : (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal
      (expectation (independentPair p q) (independentPair_support_finite p q hp hq)
        (fun z ↦ sumCutOddsLoss p q hp hq x y (x z.1 + u) z))) =
      ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal
      (expectation (independentPair p q) (independentPair_support_finite p q hp hq)
        (fun z ↦ forwardCutOdds p hp x u z.1 * backwardCutOdds q hq y u z.2)) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    congr 1
    apply expectation_congr
    intro z _
    exact sumCutOddsLoss_right p q hp hq x y z hu
  rw [hl, hr]
  apply (add_le_add (lintegral_expectation_cut_odds_product_rev_le p q hp hq x y)
    (lintegral_expectation_cut_odds_product_le p q hp hq x y)).trans_eq
  have hc : 0 ≤ 9 / 2 * (FiniteLaw.dispersion p hp x + FiniteLaw.dispersion q hq y) :=
    mul_nonneg (by norm_num) (add_nonneg (FiniteLaw.dispersion_nonneg p hp x)
      (FiniteLaw.dispersion_nonneg q hq y))
  rw [← ENNReal.ofReal_add hc hc]
  congr 1
  ring

theorem lintegral_conditional_sum_cut_entropy_le {α β : Type*} (p : PMF α) (q : PMF β)
    (hp : p.support.Finite) (hq : q.support.Finite) (x : α → ℝ) (y : β → ℝ) :
    (∫⁻ a, ENNReal.ofReal
      (conditionalCutEntropy (independentPair p q) (independentPair_support_finite p q hp hq)
        (fun z ↦ x z.1 + y z.2) (fun z ↦ x z.1) a)) ≤
      ENNReal.ofReal (9 * (FiniteLaw.dispersion p hp x + FiniteLaw.dispersion q hq y)) := by
  apply le_trans _ (lintegral_sumCutOddsLoss_le p q hp hq x y)
  apply lintegral_mono_ae
  filter_upwards [ae_cut_not_support_atom p hp x] with a ha
  exact ENNReal.ofReal_le_ofReal (conditional_sum_cut_entropy_le_odds p q hp hq x y a ha)

theorem integrable_conditional_sum_cut_entropy {α β : Type*} (p : PMF α) (q : PMF β)
    (hp : p.support.Finite) (hq : q.support.Finite) (x : α → ℝ) (y : β → ℝ) :
    Integrable (conditionalCutEntropy (independentPair p q)
      (independentPair_support_finite p q hp hq) (fun z ↦ x z.1 + y z.2) (fun z ↦ x z.1)) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (measurable_conditionalCutEntropy _ _ _ _).aestronglyMeasurable
    (Filter.Eventually.of_forall (conditionalCutEntropy_nonneg _ _ _ _))).mp
  exact ne_of_lt ((lintegral_conditional_sum_cut_entropy_le p q hp hq x y).trans_lt
    ENNReal.ofReal_lt_top)

/-- The cumulative-entropy estimate for genuine independent finite laws. -/
theorem integral_conditional_sum_cut_entropy_le {α β : Type*} (p : PMF α) (q : PMF β)
    (hp : p.support.Finite) (hq : q.support.Finite) (x : α → ℝ) (y : β → ℝ) :
    (∫ a, conditionalCutEntropy (independentPair p q)
      (independentPair_support_finite p q hp hq) (fun z ↦ x z.1 + y z.2) (fun z ↦ x z.1) a) ≤
      9 * (FiniteLaw.dispersion p hp x + FiniteLaw.dispersion q hq y) := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (lintegral_conditional_sum_cut_entropy_le p q hp hq x y)
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (conditionalCutEntropy_nonneg _ _ _ _))
    (integrable_conditional_sum_cut_entropy p q hp hq x y).aestronglyMeasurable]
  have hc : 0 ≤ 9 * (FiniteLaw.dispersion p hp x + FiniteLaw.dispersion q hq y) :=
    mul_nonneg (by norm_num) (add_nonneg (FiniteLaw.dispersion_nonneg p hp x)
      (FiniteLaw.dispersion_nonneg q hq y))
  simpa only [ENNReal.toReal_ofReal hc] using h

end ExactOverlaps.Entropy
