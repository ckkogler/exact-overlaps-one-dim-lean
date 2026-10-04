module

public import ExactOverlaps.SelfSimilar.BufferedEntropyLimit
public import ExactOverlaps.SelfSimilar.StationaryTailResidual

/-! Vanishing translation entropy increments above the Lyapunov scale. -/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ExactOverlaps.SelfSimilar

theorem targetRatioLevel_mono {κ q₁ q₂ : ℝ} (hκ : 0 ≤ κ) (hq : q₁ ≤ q₂) (n : ℕ) :
    targetRatioLevel κ q₁ n ≤ targetRatioLevel κ q₂ n := by
  apply Int.floor_mono
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hq hκ) (Nat.cast_nonneg n)

namespace System

open Entropy
variable {ι : Type*} [Fintype ι]

theorem translationEntropyIncrement_nonneg (S : System ι) (n : ℕ)
    {i f : ℤ} (hif : i ≤ f) : 0 ≤ S.translationEntropyIncrement n i f :=
  sub_nonneg.mpr (dyadicEntropy_mono _ _ hif)

theorem translationEntropyIncrement_antitone_coarse (S : System ι) (n : ℕ)
    {i j f : ℤ} (hij : i ≤ j) :
    S.translationEntropyIncrement n j f ≤ S.translationEntropyIncrement n i f := by
  exact sub_le_sub_left (dyadicEntropy_mono _ _ hij) _

/-- The genuine stationary self-similar measure forces vanishing entropy gain
between the Lyapunov scale and every fixed strictly finer multiple. -/
theorem translationEntropyIncrement_div_tendsto_zero (S : System ι)
    (μ : ProbabilityMeasure ℝ) (hμ : S.IsStationary (μ : Measure ℝ))
    (hdim : (lowerHausdorffDimension (μ : Measure ℝ)).toReal < 1)
    {q : ℝ} (hq : 1 < q) :
    Tendsto (fun n : ℕ ↦
      S.translationEntropyIncrement n (targetRatioLevel S.dyadicLyapunov 1 n)
        (targetRatioLevel S.dyadicLyapunov q n) / n) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro τ hτ
  obtain ⟨e, he, heτ⟩ := exists_positive_entropy_threshold
    (κ := S.dyadicLyapunov) (q := q) hτ
  obtain ⟨γ, hγ, hbound⟩ := S.exists_eventual_buffered_translation_bound μ hμ hdim he
  obtain ⟨ε, hε, hεsmall, hgap, hsmall⟩ := exists_positive_entropy_buffer
    (d := (lowerHausdorffDimension (μ : Measure ℝ)).toReal) (γ := γ)
    S.dyadicLyapunov_pos hq (heτ.trans (half_lt_self hτ))
  have hres := S.stationaryTailEntropyResidual_div_tendsto μ hμ hε hεsmall hq
  have hupper := S.bufferedEntropyUpper_div_tendsto μ hμ e γ ε q hγ hε hres
  have hupperSmall : ∀ᶠ n : ℕ in atTop, S.bufferedEntropyUpper μ hμ e γ ε q n / n < τ :=
    hupper.eventually (gt_mem_nhds hsmall)
  filter_upwards [hbound ε q hε hq hgap, hupperSmall] with n hn hu
  have hc := S.translationEntropyIncrement_antitone_coarse n
    (f := targetRatioLevel S.dyadicLyapunov q n)
    (bufferedRatioLevel_le_target S.dyadicLyapunov_pos.le hε.le (le_refl 1) n)
  have hnonneg := div_nonneg
    (S.translationEntropyIncrement_nonneg n
      (targetRatioLevel_mono S.dyadicLyapunov_pos.le hq.le n)) (Nat.cast_nonneg n)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  exact (div_le_div_of_nonneg_right (hc.trans hn) (Nat.cast_nonneg n)).trans_lt hu

end System
end ExactOverlaps.SelfSimilar
