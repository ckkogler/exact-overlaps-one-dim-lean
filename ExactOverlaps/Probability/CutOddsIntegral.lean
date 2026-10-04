module

public import ExactOverlaps.Probability.CutOdds

/-!
# The integral of the averaged odds majorant

The exact distance-tail integral is half the dispersion. Each side of a
sample's cut therefore contributes at most nine halves of the sum of the
two marginal dispersions.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ExactOverlaps.FiniteProbability

lemma lintegral_distanceTail_majorant {α β : Type*} (p : PMF α) (q : PMF β)
    (hp : p.support.Finite) (hq : q.support.Finite) (x : α → ℝ) (y : β → ℝ) :
    (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal
      (9 * (distanceTail p hp x u + distanceTail q hq y u))) =
      ENNReal.ofReal (9 / 2 * (FiniteLaw.dispersion p hp x + FiniteLaw.dispersion q hq y)) := by
  have hi : IntegrableOn (fun u ↦ 9 * (distanceTail p hp x u + distanceTail q hq y u))
      (Ioi 0) :=
    ((integrableOn_distanceTail p hp x).add (integrableOn_distanceTail q hq y)).const_mul 9
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun u ↦ mul_nonneg (by norm_num)
      (add_nonneg (distanceTail_nonneg p hp x u) (distanceTail_nonneg q hq y u)))),
    integral_const_mul, integral_add (integrableOn_distanceTail p hp x)
      (integrableOn_distanceTail q hq y), integral_distanceTail, integral_distanceTail]
  congr 1
  ring

theorem lintegral_expectation_cut_odds_product_le {α β : Type*} (p : PMF α) (q : PMF β)
    (hp : p.support.Finite) (hq : q.support.Finite) (x : α → ℝ) (y : β → ℝ) :
    (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal
      (expectation (Entropy.independentPair p q) (Entropy.independentPair_support_finite p q hp hq)
        (fun z ↦ forwardCutOdds p hp x u z.1 * backwardCutOdds q hq y u z.2))) ≤
      ENNReal.ofReal (9 / 2 * (FiniteLaw.dispersion p hp x + FiniteLaw.dispersion q hq y)) := by
  rw [← lintegral_distanceTail_majorant p q hp hq x y]
  exact lintegral_mono_ae ((ae_expectation_cut_odds_product_le p q hp hq x y).mono
    (fun _ h ↦ ENNReal.ofReal_le_ofReal h))

theorem lintegral_expectation_cut_odds_product_rev_le {α β : Type*} (p : PMF α) (q : PMF β)
    (hp : p.support.Finite) (hq : q.support.Finite) (x : α → ℝ) (y : β → ℝ) :
    (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal
      (expectation (Entropy.independentPair p q) (Entropy.independentPair_support_finite p q hp hq)
        (fun z ↦ backwardCutOdds p hp x u z.1 * forwardCutOdds q hq y u z.2))) ≤
      ENNReal.ofReal (9 / 2 * (FiniteLaw.dispersion p hp x + FiniteLaw.dispersion q hq y)) := by
  rw [← lintegral_distanceTail_majorant p q hp hq x y]
  exact lintegral_mono_ae ((ae_expectation_cut_odds_product_rev_le p q hp hq x y).mono
    (fun _ h ↦ ENNReal.ofReal_le_ofReal h))

end ExactOverlaps.FiniteProbability
