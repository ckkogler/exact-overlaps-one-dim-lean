module

public import ExactOverlaps.SelfSimilar.StationaryApproximation
public import ExactOverlaps.SelfSimilar.StationaryTailBound
public import ExactOverlaps.SelfSimilar.RareQuantizedCoupling
public import ExactOverlaps.SelfSimilar.DyadicScaleBounds

/-!
Coarse entropy approximation at every scale slightly below the Lyapunov
scale. The coupling's atypical words contribute their actual vanishing
probability multiplied by a proved linear entropy bound.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι]

theorem buffered_entropy_error_bound (S : System ι) (ν : ProbabilityMeasure ℝ)
    (hν : S.IsStationary (ν : Measure ℝ)) {R : ℝ} (hRpos : 0 ≤ R)
    (htail : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ R) (M : ℕ) (hM : R ≤ M)
    (ε : ℝ) (hεupper : S.lyapunov + ε ≤ 0) (n : ℕ) :
    |Entropy.dyadicEntropy ν (S.hasBoundedSupport hν)
        (contractionScale (Real.exp (S.lyapunov + ε)) n) -
      Entropy.dyadicEntropy (S.wordTranslationProbability n)
        (S.wordTranslationProbability_hasBoundedSupport n)
        (contractionScale (Real.exp (S.lyapunov + ε)) n)| ≤
      Real.log 2 + Real.log (2 * M + 3 : ℝ) +
        S.logRatioDeviationProbability ε n *
          (Real.log (2 * M + 3 : ℝ) - (n : ℝ) * (S.lyapunov + ε)) := by
  let i := contractionScale (Real.exp (S.lyapunov + ε)) n
  let N : ℕ := M * 2 ^ i.toNat
  have hi : 0 ≤ i := contractionScale_nonneg (Real.exp_pos _)
    (Real.exp_le_one_iff.mpr hεupper) n
  have hfst := S.wordCoupling_map_fst_probability ν n
  have hsnd := S.wordCoupling_map_snd ν hν n
  have hX : Entropy.HasBoundedSupport ((S.wordCoupling ν n).map Prod.fst) := by
    rw [hfst]
    exact S.wordTranslationProbability_hasBoundedSupport n
  have hY : Entropy.HasBoundedSupport ((S.wordCoupling ν n).map Prod.snd) := by
    rw [hsnd]
    exact S.hasBoundedSupport hν
  have hdisp : ∀ᵐ z ∂(S.wordCoupling ν n : Measure (ℝ × ℝ)), |z.2 - z.1| ≤ R := by
    simpa only [one_pow, one_mul] using S.wordCoupling_displacement ν
      (by norm_num : (0 : ℝ) ≤ 1) (fun j ↦ (S.contracting j).le) htail n
  have hglobal : ∀ᵐ z ∂(S.wordCoupling ν n : Measure (ℝ × ℝ)),
      |(2 : ℝ) ^ i * (z.2 - z.1)| ≤ N := by
    filter_upwards [hdisp] with z hz
    rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) i)]
    calc
      (2 : ℝ) ^ i * |z.2 - z.1| ≤ (2 : ℝ) ^ i * (M : ℝ) :=
        mul_le_mul_of_nonneg_left (hz.trans hM) (zpow_nonneg (by norm_num) i)
      _ = N := by
        simp only [N, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_toNat_eq_zpow hi]
        ring
  have hrare : ((S.wordCoupling ν n : Measure (ℝ × ℝ))
      {z | (M : ℝ) < |(2 : ℝ) ^ i * (z.2 - z.1)|}).toReal ≤
        S.logRatioDeviationProbability ε n := by
    apply le_trans _ (S.wordCoupling_scaled_tail_le ν hRpos htail n ε)
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono
    intro z hz
    exact hM.trans_lt hz
  have hc := Entropy.abs_dyadicEntropy_sub_le_of_rare_coupling
    (S.wordCoupling ν n) Prod.fst Prod.snd measurable_fst measurable_snd hX hY i M N hglobal hrare
  have hc' : |Entropy.dyadicEntropy ν (S.hasBoundedSupport hν) i -
      Entropy.dyadicEntropy (S.wordTranslationProbability n)
        (S.wordTranslationProbability_hasBoundedSupport n) i| ≤
        Real.log 2 + Real.log (2 * M + 3 : ℝ) +
          S.logRatioDeviationProbability ε n * Real.log (2 * N + 3 : ℝ) := by
    simpa only [hfst, hsnd] using hc
  have hlog : Real.log (2 * N + 3 : ℝ) ≤
      Real.log (2 * M + 3 : ℝ) - (n : ℝ) * (S.lyapunov + ε) := by
    have h₁ := log_dyadic_mesh_bound M hi
    have h₂ := contractionScale_exp_mul_log_two_le (S.lyapunov + ε) n
    change Real.log (2 * N + 3 : ℝ) ≤ _ at h₁
    change (i : ℝ) * Real.log 2 ≤ _ at h₂
    linarith
  exact hc'.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hlog (S.logRatioDeviationProbability_nonneg ε n)))

/-- For every fixed positive buffer, the coarse entropy error per letter vanishes. -/
theorem buffered_entropy_error_div_tendsto_zero (S : System ι) (ν : ProbabilityMeasure ℝ)
    (hν : S.IsStationary (ν : Measure ℝ)) {ε : ℝ} (hε : 0 < ε)
    (hεupper : S.lyapunov + ε ≤ 0) :
    Tendsto (fun n : ℕ ↦
      (Entropy.dyadicEntropy ν (S.hasBoundedSupport hν)
          (contractionScale (Real.exp (S.lyapunov + ε)) n) -
        Entropy.dyadicEntropy (S.wordTranslationProbability n)
          (S.wordTranslationProbability_hasBoundedSupport n)
          (contractionScale (Real.exp (S.lyapunov + ε)) n)) / n) atTop (𝓝 0) := by
  obtain ⟨R, hRpos, hR⟩ := S.exists_closedBall_full_measure hν
  obtain ⟨M, hM⟩ := exists_nat_ge R
  have htail : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ R := by
    have hball : ∀ᵐ x ∂(ν : Measure ℝ), x ∈ Metric.closedBall (0 : ℝ) R := ae_iff.mpr hR
    filter_upwards [hball] with x hx
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hx
  let C : ℝ := Real.log 2 + Real.log (2 * M + 3 : ℝ)
  let D : ℝ := Real.log (2 * M + 3 : ℝ)
  have hupper : Tendsto (fun n : ℕ ↦ C / n + S.logRatioDeviationProbability ε n *
      (D / n - (S.lyapunov + ε))) atTop (𝓝 0) := by
    have hC := tendsto_const_div_atTop_nhds_zero_nat C
    have hD := (tendsto_const_div_atTop_nhds_zero_nat D).sub_const (S.lyapunov + ε)
    simpa only [zero_mul, add_zero] using hC.add
      ((S.logRatioDeviationProbability_tendsto_zero hε).mul hD)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  apply squeeze_zero' (Eventually.of_forall fun n ↦ abs_nonneg _) _ hupper
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [abs_div, abs_of_pos hn']
  have hb := div_le_div_of_nonneg_right
    (S.buffered_entropy_error_bound ν hν hRpos.le htail M hM ε hεupper n) hn'.le
  convert hb using 1
  dsimp [C, D]
  field_simp

end ExactOverlaps.SelfSimilar.System
