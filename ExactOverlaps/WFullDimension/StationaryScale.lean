/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.StoppedStationarity
public import ExactOverlaps.StoppedConcatenation.ThresholdWordLaw
public import ExactOverlaps.ConvolutionDisintegration.Affine
public import ExactOverlaps.ConvolutionDisintegration.ScalePower
public import ExactOverlaps.WFullDimension.ScaleLimit

/-!
The exact scale comparison for a stationary measure follows from a genuine
bounded first-crossing word law. All weights are the actual stopped-word
probabilities and both orientations of affine maps are retained.
-/

@[expose] public section

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace ExactOverlaps.WFullDimension

open ConvolutionDisintegration Entropy SelfSimilar

theorem stationary_W_power_scale_bound {ι : Type*} [Fintype ι]
    (S : System ι) (μ : ProbabilityMeasure ℝ) (hμ : S.IsStationary (μ : Measure ℝ))
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    W μ s ≤ (W μ t) ^ (S.rhoMin ^ 2) := by
  classical
  let : MeasurableSpace ι := ⊤
  have : MeasurableSingletonClass ι := ⟨fun _ ↦ trivial⟩
  have ht : 0 < t := hs.trans_le hst
  have hu : 0 < s / t := div_pos hs ht
  have hu1 : s / t ≤ 1 := (div_le_one ht).mpr hst
  let T := S.ratioCrossingRule (s / t) hu
  let p := T.stoppedWordLaw S.alphabetLaw
  let : Fintype p.support := (T.stoppedWordLaw_support_finite S.alphabetLaw).fintype
  have hbound (w : p.support) :
      W (μ.map (S.wordMap w.val.1 w.val.2)) s ≤ (W μ t) ^ (S.rhoMin ^ 2) := by
    have hb := S.ratioCrossingWordLaw_bounds (s / t) hu hu1 w
    let a := |S.wordRatio w.val.1 w.val.2|
    have ha : 0 < a := abs_pos.mpr (S.wordRatio_ne_zero _ _)
    have hta : t * a ≤ s := by
      have hh := (le_div_iff₀ ht).mp hb.2
      change a * t ≤ s at hh
      nlinarith
    have hrat : S.rhoMin * s ≤ t * a := by
      have hh := (mul_lt_mul_iff_left₀ ht).mpr hb.1
      change (S.rhoMin * (s / t)) * t < a * t at hh
      have he : (S.rhoMin * (s / t)) * t = S.rhoMin * s := by field_simp
      rw [he] at hh
      nlinarith
    have hts : t ≤ s / a := (le_div_iff₀ ha).mpr hta
    have hrho : S.rhoMin * (s / a) ≤ t := by
      rw [← mul_div_assoc]
      exact (div_le_iff₀ ha).mpr hrat
    have he : S.rhoMin ^ 2 ≤ t ^ 2 / (s / a) ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos (div_pos hs ha))).mpr
      have hh := mul_self_le_mul_self
        (mul_nonneg S.rhoMin_pos.le (div_pos hs ha).le) hrho
      nlinarith
    change W (μ.map (fun x ↦ (S.wordMap w.val.1 w.val.2).ratio * x +
      (S.wordMap w.val.1 w.val.2).shift)) s ≤ _
    rw [W_map_affine (S.wordMap _ _).ratio_ne_zero hs]
    exact (W_scale_power_le ht hts μ).trans
      (Real.rpow_le_rpow_of_exponent_ge' (W_nonneg ht.le μ) (W_le_one ht.le μ)
        (sq_nonneg _) he)
  have hh := S.W_le_stoppedWord_average T μ hμ hs.le
  apply hh.trans
  calc
    _ ≤ ∑ w : p.support, (p w).toReal * (W μ t) ^ (S.rhoMin ^ 2) :=
      Finset.sum_le_sum (fun w _ ↦ mul_le_mul_of_nonneg_left (hbound w) ENNReal.toReal_nonneg)
    _ = (W μ t) ^ (S.rhoMin ^ 2) := by
      rw [← Finset.sum_mul]
      have hp : ∑ w : p.support, (p w).toReal = 1 := by
        simpa only [supportLaw_apply] using sum_pmf_toReal (supportLaw p)
      rw [hp, one_mul]

theorem stationary_W_tendsto_zero_of_sequence {ι : Type*} [Fintype ι]
    (S : System ι) (μ : ProbabilityMeasure ℝ) (hμ : S.IsStationary (μ : Measure ℝ))
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n)
    (hW : Tendsto (fun n ↦ W μ (r n)) atTop (𝓝 0)) :
    Tendsto (W μ) (𝓝[>] 0) (𝓝 0) :=
  tendsto_zero_of_power_scale_bound (sq_pos_of_pos S.rhoMin_pos)
    (fun _s hs ↦ W_nonneg hs.le μ)
    (fun _ _ hs hst ↦ stationary_W_power_scale_bound S μ hμ hs hst) hr hW

end ExactOverlaps.WFullDimension
