module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Integrating nonnegative finite weighted averages

These identities keep the integral in ENNReal, allowing infinite integrals.
They are used when averaging a bound over positive-mass conditional laws.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace ExactOverlaps.FiniteProbability

lemma lintegral_ofReal_sum_mul {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (μ : Measure Ω) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (f : ι → Ω → ℝ)
    (hm : ∀ i, Measurable (f i)) (hn : ∀ i, ∀ᵐ x ∂μ, 0 ≤ f i x) :
    (∫⁻ x, ENNReal.ofReal (∑ i, w i * f i x) ∂μ) =
      ∑ i, ENNReal.ofReal (w i) * ∫⁻ x, ENNReal.ofReal (f i x) ∂μ := by
  calc
    (∫⁻ x, ENNReal.ofReal (∑ i, w i * f i x) ∂μ) =
        ∫⁻ x, ∑ i, ENNReal.ofReal (w i) * ENNReal.ofReal (f i x) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [Filter.eventually_all.mpr hn] with x hx
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ mul_nonneg (hw i) (hx i))]
      simp_rw [ENNReal.ofReal_mul (hw _)]
    _ = ∑ i, ∫⁻ x, ENNReal.ofReal (w i) * ENNReal.ofReal (f i x) ∂μ :=
      lintegral_finsetSum _ (fun i _ ↦ ((hm i).ennreal_ofReal).const_mul _)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- A nonnegative integral bound survives finite nonnegative averaging. -/
lemma ofReal_sum_mul_le_lintegral {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (μ : Measure Ω) (w d : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hd : ∀ i, 0 ≤ d i)
    (f : ι → Ω → ℝ) (hm : ∀ i, Measurable (f i))
    (hn : ∀ i, ∀ᵐ x ∂μ, 0 ≤ f i x) (C : ℝ≥0∞)
    (h : ∀ i, ENNReal.ofReal (d i) ≤ C * ∫⁻ x, ENNReal.ofReal (f i x) ∂μ) :
    ENNReal.ofReal (∑ i, w i * d i) ≤
      C * ∫⁻ x, ENNReal.ofReal (∑ i, w i * f i x) ∂μ := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ mul_nonneg (hw i) (hd i)),
    lintegral_ofReal_sum_mul μ w hw f hm hn]
  simp_rw [ENNReal.ofReal_mul (hw _)]
  calc
    (∑ i, ENNReal.ofReal (w i) * ENNReal.ofReal (d i)) ≤
        ∑ i, ENNReal.ofReal (w i) * (C * ∫⁻ x, ENNReal.ofReal (f i x) ∂μ) :=
      Finset.sum_le_sum (fun i _ ↦ mul_le_mul_of_nonneg_left (h i) zero_le)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

end ExactOverlaps.FiniteProbability
