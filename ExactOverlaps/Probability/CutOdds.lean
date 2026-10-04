module

public import ExactOverlaps.Entropy.CutEntropy
public import ExactOverlaps.Probability.CDFReflection
public import ExactOverlaps.Probability.IndependentExpectations

/-!
# Averaged cut-prediction odds

For each positive displacement, independence separates the forward odds of
one marginal from the backward odds of the other. The two cumulative bounds
then give the exact pointwise majorant used to integrate prediction loss.
-/

@[expose] public section

open MeasureTheory Set
open scoped Classical

namespace ExactOverlaps.FiniteProbability

noncomputable def forwardCutOdds {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (x : α → ℝ) (u : ℝ) (a : α) : ℝ :=
  Real.sqrt ((1 - cumulativeMass p hp x (x a + u)) / cumulativeMass p hp x (x a + u))

noncomputable def backwardCutOdds {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (x : α → ℝ) (u : ℝ) (a : α) : ℝ :=
  Real.sqrt (cumulativeMass p hp x (x a - u) / (1 - cumulativeMass p hp x (x a - u)))

lemma measurable_forwardCutOdds {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (x : α → ℝ) (a : α) : Measurable (fun u ↦ forwardCutOdds p hp x u a) := by
  have h : Measurable (fun u : ℝ ↦ cumulativeMass p hp x (x a + u)) :=
    (Entropy.measurable_cumulativeMass p hp x).comp (measurable_const.add measurable_id)
  exact ((measurable_const.sub h).div h).sqrt

lemma measurable_backwardCutOdds {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (x : α → ℝ) (a : α) : Measurable (fun u ↦ backwardCutOdds p hp x u a) := by
  have h : Measurable (fun u : ℝ ↦ cumulativeMass p hp x (x a - u)) :=
    (Entropy.measurable_cumulativeMass p hp x).comp (measurable_const.sub measurable_id)
  exact (h.div (measurable_const.sub h)).sqrt

lemma sqrt_tail_product_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (3 * Real.sqrt (2 * a)) * (3 * Real.sqrt (2 * b)) ≤ 9 * (a + b) := by
  have hsa := Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ha)
  have hsb := Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hb)
  nlinarith [sq_nonneg (Real.sqrt (2 * a) - Real.sqrt (2 * b))]

theorem ae_expectation_cut_odds_product_le {α β : Type*} (p : PMF α) (q : PMF β)
    (hp : p.support.Finite) (hq : q.support.Finite) (x : α → ℝ) (y : β → ℝ) :
    ∀ᵐ u : ℝ ∂volume.restrict (Ioi 0),
      expectation (Entropy.independentPair p q) (Entropy.independentPair_support_finite p q hp hq)
        (fun z ↦ forwardCutOdds p hp x u z.1 * backwardCutOdds q hq y u z.2) ≤
      9 * (distanceTail p hp x u + distanceTail q hq y u) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi,
    ae_reflected_cdf_sqrt_odds_le q hq y] with u hu hb
  rw [expectation_independentPair_mul]
  have hf := cdf_sqrt_odds_le_statistic p hp x hu.le
  have hf' : expectation p hp (forwardCutOdds p hp x u) ≤
      3 * Real.sqrt (2 * distanceTail p hp x u) := hf
  have hb' : expectation q hq (backwardCutOdds q hq y u) ≤
      3 * Real.sqrt (2 * distanceTail q hq y u) := hb
  exact (mul_le_mul hf' hb'
    (expectation_nonneg q hq (fun _ _ ↦ Real.sqrt_nonneg _)) (by positivity)).trans
    (sqrt_tail_product_le (distanceTail_nonneg p hp x u) (distanceTail_nonneg q hq y u))

theorem ae_expectation_cut_odds_product_rev_le {α β : Type*} (p : PMF α) (q : PMF β)
    (hp : p.support.Finite) (hq : q.support.Finite) (x : α → ℝ) (y : β → ℝ) :
    ∀ᵐ u : ℝ ∂volume.restrict (Ioi 0),
      expectation (Entropy.independentPair p q) (Entropy.independentPair_support_finite p q hp hq)
        (fun z ↦ backwardCutOdds p hp x u z.1 * forwardCutOdds q hq y u z.2) ≤
      9 * (distanceTail p hp x u + distanceTail q hq y u) := by
  filter_upwards [ae_expectation_cut_odds_product_le q p hq hp y x] with u hu
  rw [expectation_independentPair_mul q p hq hp] at hu
  rw [expectation_independentPair_mul p q hp hq]
  simpa only [mul_comm, add_comm] using hu

end ExactOverlaps.FiniteProbability
