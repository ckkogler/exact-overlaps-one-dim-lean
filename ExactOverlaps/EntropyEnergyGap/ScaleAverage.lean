module

public import ExactOverlaps.EntropyEnergyGap.ConditionalEntropyLoss
public import ExactOverlaps.EntropyEnergyGap.QuantizedEnergy
public import ExactOverlaps.ScaleEntropy.FiniteLaw

/-!
# From entropy of an independent sum to variance energy below a scale

Apply the genuine entropy-loss theorem after every mesh-label observation,
use the exact one-half conditional-energy tail, and average over physical
translations. All conditional entropy integrals are justified by the
finite-law averaged Shannon chain rule.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators Classical
open ExactOverlaps.Entropy ExactOverlaps.FiniteProbability ExactOverlaps.VarianceEnergy
open ExactOverlaps.ScaleEntropy

namespace ExactOverlaps.EntropyEnergyGap

lemma quantized_conditional_entropy_bound (p : PMF ℝ) (hp : p.support.Finite)
    (m : ℕ) (C : ℝ)
    (hC : tupleSumEntropy m (iidTupleLaw p m) (iidTupleLaw_support_finite p hp m) ≤ C)
    {R : ℝ} (hR : 0 < R) (t : ℝ) :
    m * conditionalEntropy p hp (quantize R t) ≤
      C + 30 * m ^ 2 * ((energyBelow p.toMeasure R).toReal + 1 / 2) := by
  have h := iid_conditional_entropy_le m p hp (quantize R t)
  exact h.trans (add_le_add hC (mul_le_mul_of_nonneg_left (mean_quantized_energy_le p hp hR t)
    (by positivity)))

lemma entropy_gap_mul_le (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ)
    (p : PMF ℝ) (hp : p.support.Finite) (hμp : (μ : Measure ℝ) = p.toMeasure)
    (m : ℕ) (C : ℝ)
    (hC : tupleSumEntropy m (iidTupleLaw p m) (iidTupleLaw_support_finite p hp m) ≤ C)
    {R : ℝ} (hR : 0 < R) :
    m * (finiteEntropy p hp - entropy μ hμ R hR) ≤
      C + 30 * m ^ 2 * ((energyBelow p.toMeasure R).toReal + 1 / 2) := by
  have hInt := intervalIntegral.integral_mono_on hR.le
    ((intervalIntegrable_finiteConditional μ hμ p hp hμp R hR 0 R).const_mul (m : ℝ))
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ ↦ C + 30 * m ^ 2 * ((energyBelow p.toMeasure R).toReal + 1 / 2)) volume 0 R)
    (fun t _ ↦ quantized_conditional_entropy_bound p hp m C hC hR t)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hInt
  simp only [sub_zero, smul_eq_mul] at hInt
  have hchain := finiteEntropy_sub_entropy_eq_average_conditional μ hμ p hp hμp R hR
  have hI : (∫ t in (0 : ℝ)..R, conditionalEntropy p hp (quantize R t)) =
      (finiteEntropy p hp - entropy μ hμ R hR) * R :=
    (div_eq_iff hR.ne').mp hchain.symm
  rw [hI] at hInt
  apply (mul_le_mul_iff_of_pos_left hR).mp
  nlinarith [hInt]

theorem energyBelow_ge_entropy_gap (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ)
    (p : PMF ℝ) (hp : p.support.Finite) (hμp : (μ : Measure ℝ) = p.toMeasure)
    (m : ℕ) (hm : 0 < m) (C : ℝ)
    (hC : tupleSumEntropy m (iidTupleLaw p m) (iidTupleLaw_support_finite p hp m) ≤ C)
    {R : ℝ} (hR : 0 < R) :
    1 / (30 * m) * (finiteEntropy p hp - entropy μ hμ R hR - C / m) - 1 / 2 ≤
      (energyBelow p.toMeasure R).toReal := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h := entropy_gap_mul_le μ hμ p hp hμp m C hC hR
  have hgap : finiteEntropy p hp - entropy μ hμ R hR - C / m ≤
      30 * m * ((energyBelow p.toMeasure R).toReal + 1 / 2) := by
    apply (mul_le_mul_iff_of_pos_right hm').mp
    have he := div_mul_cancel₀ C hm'.ne'
    nlinarith [h]
  calc
    _ ≤ (1 / (30 * m)) * (30 * m * ((energyBelow p.toMeasure R).toReal + 1 / 2)) - 1 / 2 :=
      sub_le_sub_right (mul_le_mul_of_nonneg_left hgap (by positivity)) _
    _ = _ := by field_simp; ring

end ExactOverlaps.EntropyEnergyGap
