module

public import ExactOverlaps.SelfSimilar.StationaryCoupling
public import ExactOverlaps.SelfSimilar.LyapunovConcentration
public import ExactOverlaps.SelfSimilar.ContractionScale

/-!
Exceptional displacements of the actual word-tail coupling are controlled
by exceptional logarithmic contraction. This yields a probability bound at
the buffered Lyapunov scale for systems with unequal contraction factors.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal Classical BigOperators

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι]

theorem wordCoupling_tail_le (S : System ι) (ν : ProbabilityMeasure ℝ)
    {R : ℝ} (hR : ∀ᵐ z ∂(ν : Measure ℝ), |z| ≤ R) (n : ℕ) (a : ℝ) :
    (S.wordCoupling ν n : Measure (ℝ × ℝ)) {z | a < |z.2 - z.1|} ≤
      (S.wordLaw n).toOuterMeasure {w | a < |S.wordRatio n w| * R} := by
  have hm : Measurable (fun z : ℝ × ℝ ↦ |z.2 - z.1|) := by fun_prop
  change S.wordCouplingMeasure ν n {z | a < |z.2 - z.1|} ≤ _
  rw [S.wordCouplingMeasure_apply ν n (measurableSet_lt measurable_const hm),
    PMF.toOuterMeasure_apply_fintype]
  apply Finset.sum_le_sum
  intro w _
  change S.wordWeight n w * (ν : Measure ℝ)
    {z | a < |S.wordMap n w z - S.wordTranslation n w|} ≤
      if a < |S.wordRatio n w| * R then S.wordWeight n w else 0
  by_cases hw : a < |S.wordRatio n w| * R
  · rw [ite_eq_left hw]
    calc
      _ ≤ S.wordWeight n w * 1 := by gcongr; exact prob_le_one
      _ = S.wordWeight n w := mul_one _
  · have hz : (ν : Measure ℝ) {z | a < |S.wordMap n w z - S.wordTranslation n w|} = 0 := by
      have hae : ∀ᵐ z ∂(ν : Measure ℝ), |S.wordMap n w z - S.wordTranslation n w| ≤ a := by
        filter_upwards [hR] with z hz
        have he : S.wordMap n w z - S.wordTranslation n w = S.wordRatio n w * z := by
          simp only [wordTranslation, wordRatio]
          ring
        rw [he, abs_mul]
        exact (mul_le_mul_of_nonneg_left hz (abs_nonneg _)).trans (le_of_not_gt hw)
      simpa only [not_le] using ae_iff.mp hae
    simp only [ite_eq_right hw, hz, mul_zero, le_refl]

theorem wordCoupling_lyapunov_tail_le (S : System ι) (ν : ProbabilityMeasure ℝ)
    {R : ℝ} (hRpos : 0 ≤ R) (hR : ∀ᵐ z ∂(ν : Measure ℝ), |z| ≤ R)
    (n : ℕ) (ε : ℝ) :
    ((S.wordCoupling ν n : Measure (ℝ × ℝ))
      {z | Real.exp ((n : ℝ) * (S.lyapunov + ε)) * R < |z.2 - z.1|}).toReal ≤
      S.logRatioDeviationProbability ε n := by
  let E : Set (Word ι n) := {w | (n : ℝ) * ε ≤ |S.centeredWordLogRatio n w|}
  have hsub : {w | Real.exp ((n : ℝ) * (S.lyapunov + ε)) * R < |S.wordRatio n w| * R} ⊆ E := by
    intro w hw
    by_contra hnot
    have hgood := (S.wordRatio_typical_iff ε n w).mpr (lt_of_not_ge hnot)
    exact (not_lt_of_ge (mul_le_mul_of_nonneg_right hgood.2.le hRpos)) hw
  have hbound := (S.wordCoupling_tail_le ν hR n
    (Real.exp ((n : ℝ) * (S.lyapunov + ε)) * R)).trans
      ((S.wordLaw n).toOuterMeasure.mono hsub)
  have hfinite : (S.wordLaw n).toOuterMeasure E ≠ ⊤ := by
    rw [PMF.toOuterMeasure_apply]
    exact (S.wordLaw n).tsum_coe_indicator_ne_top E
  have h := ENNReal.toReal_mono hfinite hbound
  rw [S.logRatioDeviationProbability_eq_mass ε n] at h
  exact h

/-- At the buffered Lyapunov scale, a stationary tail exceeds R cells only on rare words. -/
theorem wordCoupling_scaled_tail_le (S : System ι) (ν : ProbabilityMeasure ℝ)
    {R : ℝ} (hRpos : 0 ≤ R) (hR : ∀ᵐ z ∂(ν : Measure ℝ), |z| ≤ R)
    (n : ℕ) (ε : ℝ) :
    ((S.wordCoupling ν n : Measure (ℝ × ℝ))
      {z | R < |(2 : ℝ) ^ contractionScale (Real.exp (S.lyapunov + ε)) n *
        (z.2 - z.1)|}).toReal ≤ S.logRatioDeviationProbability ε n := by
  let i := contractionScale (Real.exp (S.lyapunov + ε)) n
  have hscale : (2 : ℝ) ^ i * Real.exp ((n : ℝ) * (S.lyapunov + ε)) ≤ 1 := by
    rw [Real.exp_nat_mul]
    exact contractionScale_mul_pow_le_one (Real.exp_pos _) n
  have hsub : {z : ℝ × ℝ | R < |(2 : ℝ) ^ i * (z.2 - z.1)|} ⊆
      {z | Real.exp ((n : ℝ) * (S.lyapunov + ε)) * R < |z.2 - z.1|} := by
    intro z hz
    by_contra hnot
    have hsmall : |z.2 - z.1| ≤ Real.exp ((n : ℝ) * (S.lyapunov + ε)) * R := le_of_not_gt hnot
    have hsmall' : |(2 : ℝ) ^ i * (z.2 - z.1)| ≤ R := by
      rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) i)]
      calc
        (2 : ℝ) ^ i * |z.2 - z.1| ≤
            (2 : ℝ) ^ i * (Real.exp ((n : ℝ) * (S.lyapunov + ε)) * R) :=
          mul_le_mul_of_nonneg_left hsmall (zpow_nonneg (by norm_num) i)
        _ = ((2 : ℝ) ^ i * Real.exp ((n : ℝ) * (S.lyapunov + ε))) * R := (mul_assoc _ _ _).symm
        _ ≤ 1 * R := mul_le_mul_of_nonneg_right hscale hRpos
        _ = R := one_mul R
    exact (not_lt_of_ge hsmall') hz
  exact (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)).trans
    (S.wordCoupling_lyapunov_tail_le ν hRpos hR n ε)

end ExactOverlaps.SelfSimilar.System
