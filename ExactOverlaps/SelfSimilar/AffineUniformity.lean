module

public import ExactOverlaps.SelfSimilar.AffineUniformLower
public import ExactOverlaps.SelfSimilar.AffineMeanEntropy
public import ExactOverlaps.SelfSimilar.UniformEntropyPrefix

/-!
Uniform entropy dimension simultaneously over signed affine maps whose
absolute ratios lie in a fixed compact subinterval of the positive reals.
The eventual scale threshold is independent of both map and translation.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ExactOverlaps.SelfSimilar.System

open Entropy
variable {ι : Type*} [Fintype ι]

theorem uniform_affine_entropy_concentration (S : System ι) (μ : ProbabilityMeasure ℝ)
    [NullSingletonClass (μ : Measure ℝ)] (hμ : S.IsStationary (μ : Measure ℝ))
    {d : ℝ} (hd : d ≤ 1)
    (hlim : Tendsto (normalizedDyadicEntropy μ (S.hasBoundedSupport hμ)) atTop (𝓝 d))
    {a : ℝ} (ha : 0 < a) (K : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → 0 < m → ∀ᶠ n : ℕ in atTop,
      ∀ g : RealSimilarity, a ≤ |g.ratio| → |g.ratio| ≤ K →
        levelEntropyDeviationMass (μ.map g) (g.hasBoundedSupport_map μ (S.hasBoundedSupport hμ))
          n m d ε < ε := by
  let δ : ℝ := ε * ε / 32
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨M, hM⟩ := S.uniform_affine_entropy_lower_tail μ hμ hd hlim hδ
  obtain ⟨L, hL⟩ := pow_unbounded_of_one_lt (1 / a) (by norm_num : (1 : ℝ) < 2)
  have hLa : 1 ≤ (2 : ℝ) ^ L * a := ((div_lt_iff₀ ha).mp hL).le
  refine ⟨M, fun m hm hmpos ↦ ?_⟩
  have hmean := eventually_uniform_affine_mean_lt μ (S.hasBoundedSupport hμ) hlim K hmpos
    (show 0 < ε * ε / 4 from by positivity)
  have hpref : ∀ᶠ n : ℕ in atTop, 2 * (L : ℝ) / n < ε * ε / 4 :=
    (tendsto_const_div_atTop_nhds_zero_nat (2 * (L : ℝ))).eventually
      (gt_mem_nhds (by positivity : (0 : ℝ) < ε * ε / 4))
  filter_upwards [eventually_gt_atTop 0, eventually_ge_atTop L, hmean, hpref]
    with n hn hLn hmean' hpref'
  intro g hga hgK
  have hlow (i : ℕ) (hLi : L ≤ i) :
      componentEntropyBelowMass (μ.map g) (g.hasBoundedSupport_map μ (S.hasBoundedSupport hμ))
        i m d δ ≤ δ := by
    apply hM m hm hmpos g i
    rw [zpow_natCast]
    exact hLa.trans (mul_le_mul (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hLi)
      hga ha.le (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) i))
  have hdev := level_deviation_le_of_eventual_lower_tail (μ.map g)
    (g.hasBoundedSupport_map μ (S.hasBoundedSupport hμ)) hn hLn m hd hδ.le ε hlow
  have hmeanG := hmean' g hgK
  have hsmall : ε * levelEntropyDeviationMass (μ.map g)
      (g.hasBoundedSupport_map μ (S.hasBoundedSupport hμ)) n m d ε < ε * ε := by
    dsimp [δ] at hdev
    nlinarith [mul_pos hε hε]
  exact (mul_lt_mul_iff_right₀ hε).mp hsmall

/-- Uniform concentration for the standard dimension, including the atomic or
zero-dimensional case, across an entire bounded family of signed affine images. -/
theorem uniform_affine_entropy_dimension (S : System ι) (μ : ProbabilityMeasure ℝ)
    (hμ : S.IsStationary (μ : Measure ℝ)) {a : ℝ} (ha : 0 < a) (K : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → 0 < m → ∀ᶠ n : ℕ in atTop,
      ∀ g : RealSimilarity, a ≤ |g.ratio| → |g.ratio| ≤ K →
        levelEntropyDeviationMass (μ.map g) (g.hasBoundedSupport_map μ (S.hasBoundedSupport hμ))
          n m (lowerHausdorffDimension (μ : Measure ℝ)).toReal ε < ε := by
  let d : ℝ := (lowerHausdorffDimension (μ : Measure ℝ)).toReal
  have hlim : Tendsto (normalizedDyadicEntropy μ (S.hasBoundedSupport hμ)) atTop (𝓝 d) :=
    S.normalizedDyadicEntropy_tendsto_dimension μ hμ
  by_cases hz : d = 0
  · change ∃ M : ℕ, ∀ m : ℕ, M ≤ m → 0 < m → ∀ᶠ n : ℕ in atTop,
      ∀ g : RealSimilarity, a ≤ |g.ratio| → |g.ratio| ≤ K →
        levelEntropyDeviationMass (μ.map g) (g.hasBoundedSupport_map μ (S.hasBoundedSupport hμ))
          n m d ε < ε
    rw [hz] at hlim ⊢
    refine ⟨0, fun m _ hm ↦ ?_⟩
    filter_upwards [eventually_uniform_affine_mean_lt μ (S.hasBoundedSupport hμ) hlim K hm
      (show 0 < ε * ε from mul_pos hε hε)] with n hn
    intro g _ hgK
    have h := mul_levelEntropyTailMass_le (μ.map g)
      (g.hasBoundedSupport_map μ (S.hasBoundedSupport hμ)) n m ε
    have he : levelEntropyDeviationMass (μ.map g)
        (g.hasBoundedSupport_map μ (S.hasBoundedSupport hμ)) n m 0 ε =
        levelEntropyTailMass (μ.map g) (g.hasBoundedSupport_map μ (S.hasBoundedSupport hμ)) n m ε := by
      simp only [levelEntropyDeviationMass, levelEntropyTailMass,
        componentEntropyDeviationMass_zero_dimension]
    rw [he]
    exact (mul_lt_mul_iff_right₀ hε).mp (h.trans_lt (by simpa only [zero_add] using hn g hgK))
  have hpos : 0 < lowerHausdorffDimension (μ : Measure ℝ) := by
    apply pos_iff_ne_zero.mpr
    intro he
    apply hz
    dsimp [d]
    rw [he, ENNReal.toReal_zero]
  have : NullSingletonClass (μ : Measure ℝ) :=
    nullSingletonClass_of_lowerHausdorffDimension_pos _ hpos
  have hd : d ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one
    (by simpa only [ENNReal.ofReal_one] using lowerHausdorffDimension_le_one (μ : Measure ℝ))
  exact S.uniform_affine_entropy_concentration μ hμ hd hlim ha K hε

end ExactOverlaps.SelfSimilar.System
