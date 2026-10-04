module

public import ExactOverlaps.SelfSimilar.UniformAffineInverse
public import ExactOverlaps.SelfSimilar.AffineConvolution

/-!
The uniform affine inverse extends from unit-supported stationary copies
to copies carried by any fixed bounded interval. One common affine change
of coordinates preserves convolution and costs a proved vanishing entropy
error. The translation summand remains an arbitrary unit-supported law.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace ExactOverlaps.SelfSimilar.System

open Entropy
variable {ι : Type*} [Fintype ι]

theorem exists_bounded_affine_inverse (S : System ι) (μ : ProbabilityMeasure ℝ)
    (hμ : S.IsStationary (μ : Measure ℝ))
    (hdim : (lowerHausdorffDimension (μ : Measure ℝ)).toReal < 1)
    {a e R : ℝ} (ha : 0 < a) (K : ℕ) (he : 0 < e) (hR : 0 ≤ R) :
    ∃ γ > 0, ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ∀ (g : RealSimilarity) (ν : ProbabilityMeasure ℝ) (hν : HasBoundedSupport ν),
      a ≤ |g.ratio| → |g.ratio| ≤ K →
      (∀ᵐ x ∂(μ.map g : Measure ℝ), x ∈ Icc (-R) R) →
      (∀ᵐ x ∂(ν : Measure ℝ), x ∈ Icc (0 : ℝ) 1) →
      e < normalizedDyadicEntropy ν hν n →
      normalizedDyadicEntropy (μ.map g) (g.hasBoundedSupport_map μ (S.hasBoundedSupport hμ)) n + γ ≤
        normalizedDyadicEntropy (realConvolution (μ.map g) ν)
          (realConvolution_hasBoundedSupport _ _
            (g.hasBoundedSupport_map μ (S.hasBoundedSupport hμ)) hν) n := by
  let D : ℝ := 2 * R + 1
  have hD : 0 < D := by dsimp [D]; linarith
  have hD1 : 1 ≤ D := by dsimp [D]; linarith
  let s : ℝ := D⁻¹
  have hs : 0 < s := inv_pos.mpr hD
  have hs1 : s ≤ 1 := (inv_le_one₀ hD).mpr hD1
  have hsD : s * D = 1 := inv_mul_cancel₀ hD.ne'
  let f : RealSimilarity := ⟨s, hs.ne', s * R⟩
  let q : RealSimilarity := ⟨s, hs.ne', 0⟩
  obtain ⟨L, hL⟩ := exists_nat_ge (max 1 D)
  have hfL : |f.ratio| ≤ L := by
    change |s| ≤ L
    rw [abs_of_pos hs]
    exact hs1.trans ((le_max_left _ _).trans hL)
  have hinvL : |f.ratio|⁻¹ ≤ L := by
    change |D⁻¹|⁻¹ ≤ L
    rw [abs_inv, inv_inv, abs_of_pos hD]
    exact (le_max_right _ _).trans hL
  have hqinvL : |q.ratio|⁻¹ ≤ L := hinvL
  obtain ⟨γ, hγ, N₀, hN₀, hgain⟩ := S.exists_uniform_affine_inverse μ hμ hdim
    (mul_pos hs ha) K (half_pos he)
  let E : ℕ → ℝ := fun n ↦ Real.log (2 * L + 3 : ℝ) / ((n : ℝ) * Real.log 2)
  have hE : Tendsto E atTop (𝓝 0) := by
    have h := tendsto_const_div_atTop_nhds_zero_nat (Real.log (2 * L + 3 : ℝ) / Real.log 2)
    convert h using 1
    funext n
    dsimp [E]
    ring
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp
    (hE.eventually (gt_mem_nhds (lt_min (half_pos he) (by positivity : 0 < γ / 4))))
  refine ⟨γ / 2, half_pos hγ, max N₀ N₁, lt_of_lt_of_le hN₀ (le_max_left _ _), ?_⟩
  intro n hn g ν hν hga hgK htail hνunit hent
  have hn₀ : N₀ ≤ n := (le_max_left _ _).trans hn
  have hn₁ : N₁ ≤ n := (le_max_right _ _).trans hn
  have hEe : E n < e / 2 := (hN₁ n hn₁).trans_le (min_le_left _ _)
  have hEγ : E n < γ / 4 := (hN₁ n hn₁).trans_le (min_le_right _ _)
  have hfglo : s * a ≤ |(f.comp g).ratio| := by
    rw [RealSimilarity.comp_ratio, abs_mul]
    change s * a ≤ |s| * |g.ratio|
    rw [abs_of_pos hs]
    exact mul_le_mul_of_nonneg_left hga hs.le
  have hfghi : |(f.comp g).ratio| ≤ K := by
    rw [RealSimilarity.comp_ratio, abs_mul]
    change |s| * |g.ratio| ≤ K
    rw [abs_of_pos hs]
    exact (mul_le_mul_of_nonneg_right hs1 (abs_nonneg _)).trans (by simpa using hgK)
  have htailUnit : ∀ᵐ x ∂(μ.map (f.comp g) : Measure ℝ), x ∈ Icc (0 : ℝ) 1 := by
    rw [f.probability_map_comp g μ, ProbabilityMeasure.toMeasure_map]
    apply (ae_map_iff f.measurable.aemeasurable measurableSet_Icc).mpr
    filter_upwards [htail] with x hx
    change 0 ≤ s * x + s * R ∧ s * x + s * R ≤ 1
    dsimp [D] at hsD
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hx.1 hs.le,
      mul_le_mul_of_nonneg_left hx.2 hs.le]
  have hνUnit : ∀ᵐ x ∂(ν.map q : Measure ℝ), x ∈ Icc (0 : ℝ) 1 := by
    rw [ProbabilityMeasure.toMeasure_map]
    apply (ae_map_iff q.measurable.aemeasurable measurableSet_Icc).mpr
    filter_upwards [hνunit] with x hx
    change 0 ≤ s * x + 0 ∧ s * x + 0 ≤ 1
    constructor <;> nlinarith [mul_nonneg hs.le hx.1,
      mul_le_mul_of_nonneg_left hx.2 hs.le]
  have hνlower := normalizedDyadicEntropy_le_affine_add ν hν q hqinvL n
  have hνent : e / 2 < normalizedDyadicEntropy (ν.map q) (q.hasBoundedSupport_map ν hν) n := by
    change normalizedDyadicEntropy ν hν n ≤ _ + E n at hνlower
    linarith
  have hgain := hgain n hn₀ (f.comp g) (ν.map q) (q.hasBoundedSupport_map ν hν)
    hfglo hfghi htailUnit hνUnit hνent
  have hconv : realConvolution ((μ.map g).map f) (ν.map q) =
      (realConvolution (μ.map g) ν).map f :=
    realConvolution_map_affine (μ.map g) ν f q f rfl rfl (by simp [q])
  simp only [f.probability_map_comp g μ, hconv] at hgain
  have htailLower := normalizedDyadicEntropy_le_affine_add (μ.map g)
    (g.hasBoundedSupport_map μ (S.hasBoundedSupport hμ)) f hinvL n
  have hconvUpper := normalizedDyadicEntropy_affine_le (realConvolution (μ.map g) ν)
    (realConvolution_hasBoundedSupport _ _ (g.hasBoundedSupport_map μ (S.hasBoundedSupport hμ)) hν)
    f hfL n
  change _ ≤ _ + E n at htailLower hconvUpper
  linarith

end ExactOverlaps.SelfSimilar.System
