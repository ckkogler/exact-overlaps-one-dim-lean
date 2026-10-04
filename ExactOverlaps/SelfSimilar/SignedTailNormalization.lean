module

public import ExactOverlaps.SelfSimilar.BoundedAffineInverse
public import ExactOverlaps.Entropy.RescaleConvolution

/-!
Exact normalization at the scale of a signed stationary tail and a translation
cell. The component convolution is transformed by a common dyadic dilation
and an integer cell shift, so its fine entropy is preserved exactly.
-/

@[expose] public section

open MeasureTheory Set

namespace ExactOverlaps.Entropy

theorem dyadicEntropy_convolution_normalized_tail_component
    (μ ν : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ) (g : RealSimilarity)
    (i : ℤ) (k : (dyadicLaw ν i).support) (m : ℕ) :
    dyadicEntropy (realConvolution (μ.map (g.dyadicScale i)) (rescaledComponent ν i k))
      (realConvolution_hasBoundedSupport _ _ ((g.dyadicScale i).hasBoundedSupport_map μ hμ)
        (rescaledComponent_hasBoundedSupport ν i k)) m =
      dyadicEntropy (realConvolution (μ.map g) (rawComponent ν i k))
        (realConvolution_hasBoundedSupport _ _ (g.hasBoundedSupport_map μ hμ)
          (rawComponent_hasBoundedSupport ν i k)) (i + m) := by
  have h := dyadicEntropy_map_componentRescale (realConvolution (μ.map g) (rawComponent ν i k))
    (realConvolution_hasBoundedSupport _ _ (g.hasBoundedSupport_map μ hμ)
      (rawComponent_hasBoundedSupport ν i k)) i k m
  simpa only [g.probability_map_dyadicScale μ i, rescaledComponent,
    realConvolution_map_componentRescale, zero_add] using h

end ExactOverlaps.Entropy

namespace ExactOverlaps.SelfSimilar.System

open Entropy
variable {ι : Type*} [Fintype ι]

theorem exists_component_entropy_gain (S : System ι) (μ : ProbabilityMeasure ℝ)
    (hμ : S.IsStationary (μ : Measure ℝ))
    (hdim : (lowerHausdorffDimension (μ : Measure ℝ)).toReal < 1)
    {e : ℝ} (he : 0 < e) :
    ∃ γ > 0, ∃ N : ℕ, 0 < N ∧ ∀ m : ℕ, N ≤ m →
      ∀ (g : RealSimilarity) (i : ℤ) (ν : ProbabilityMeasure ℝ) (k : (dyadicLaw ν i).support),
      (1 / 2 : ℝ) ≤ (2 : ℝ) ^ i * |g.ratio| → (2 : ℝ) ^ i * |g.ratio| ≤ 1 → g.shift = 0 →
      e < dyadicEntropy (rawComponent ν i k) (rawComponent_hasBoundedSupport ν i k) (i + m) /
        ((m : ℝ) * Real.log 2) →
      dyadicEntropy (μ.map g) (g.hasBoundedSupport_map μ (S.hasBoundedSupport hμ)) (i + m) +
        γ * ((m : ℝ) * Real.log 2) ≤
      dyadicEntropy (realConvolution (μ.map g) (rawComponent ν i k))
        (realConvolution_hasBoundedSupport _ _ (g.hasBoundedSupport_map μ (S.hasBoundedSupport hμ))
          (rawComponent_hasBoundedSupport ν i k)) (i + m) := by
  obtain ⟨R, hR, hfull⟩ := S.exists_closedBall_full_measure hμ
  have hsupport : ∀ᵐ x ∂(μ : Measure ℝ), |x| ≤ R := by
    have hball : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Metric.closedBall (0 : ℝ) R := mem_ae_iff.mpr hfull
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hball
  obtain ⟨γ, hγ, N, hN, hinv⟩ := S.exists_bounded_affine_inverse μ hμ hdim
    (by norm_num : (0 : ℝ) < 1 / 2) 1 he hR.le
  refine ⟨γ, hγ, N, hN, ?_⟩
  intro m hm g i ν k hratioLo hratioHi hshift hent
  have hmpos : 0 < m := lt_of_lt_of_le hN hm
  have hscale : |(g.dyadicScale i).ratio| = (2 : ℝ) ^ i * |g.ratio| := by
    simp only [RealSimilarity.dyadicScale, abs_mul,
      abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) i)]
  have htail : ∀ᵐ x ∂(μ.map (g.dyadicScale i) : Measure ℝ), x ∈ Icc (-R) R := by
    rw [ProbabilityMeasure.toMeasure_map]
    apply (ae_map_iff (g.dyadicScale i).measurable.aemeasurable measurableSet_Icc).mpr
    filter_upwards [hsupport] with x hx
    apply abs_le.mp
    change |((2 : ℝ) ^ i * g.ratio) * x + (2 : ℝ) ^ i * g.shift| ≤ R
    rw [hshift, mul_zero, add_zero, abs_mul, abs_mul,
      abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) i)]
    exact (mul_le_mul_of_nonneg_left hx (mul_nonneg (zpow_nonneg (by norm_num) i) (abs_nonneg _))).trans
      ((mul_le_mul_of_nonneg_right hratioHi hR.le).trans_eq (one_mul R))
  have hunit : ∀ᵐ x ∂(rescaledComponent ν i k : Measure ℝ), x ∈ Icc (0 : ℝ) 1 := by
    filter_upwards [ae_rescaledComponent_mem_Ico ν i k] with x hx
    exact ⟨hx.1, hx.2.le⟩
  have hent' : e < normalizedDyadicEntropy (rescaledComponent ν i k)
      (rescaledComponent_hasBoundedSupport ν i k) m := by
    simpa only [normalizedDyadicEntropy, dyadicEntropy_rescaledComponent] using hent
  have h := hinv m hm (g.dyadicScale i) (rescaledComponent ν i k)
    (rescaledComponent_hasBoundedSupport ν i k)
    (by simpa only [hscale] using hratioLo) (by simpa only [hscale, Nat.cast_one] using hratioHi)
    htail hunit hent'
  simp only [normalizedDyadicEntropy,
    dyadicEntropy_affine_scale μ (S.hasBoundedSupport hμ) g i m,
    dyadicEntropy_convolution_normalized_tail_component μ ν (S.hasBoundedSupport hμ) g i k m] at h
  have hden : 0 < (m : ℝ) * Real.log 2 :=
    mul_pos (Nat.cast_pos.mpr hmpos) (Real.log_pos (by norm_num))
  have hh := mul_le_mul_of_nonneg_right h hden.le
  simpa only [add_mul, div_mul_cancel₀ _ hden.ne'] using hh

end ExactOverlaps.SelfSimilar.System
