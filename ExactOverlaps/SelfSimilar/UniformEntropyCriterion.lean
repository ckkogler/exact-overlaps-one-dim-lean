module

public import ExactOverlaps.SelfSimilar.UniformEntropyDimension

/-!
Uniform lower tails, together with a genuine global entropy limit, imply
two-sided uniform entropy dimension. All probabilities are explicit sums
of actual component masses. The estimate is a finite expectation argument.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology ENNReal BigOperators

namespace ExactOverlaps.Entropy

/-- Mass of components with normalized entropy at most `d-δ`. -/
noncomputable def componentEntropyBelowMass (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) (m : ℕ) (d δ : ℝ) : ℝ := by
  classical
  letI : Fintype (dyadicLaw μ i).support := (dyadicLaw_support_finite μ hμ i).fintype
  exact ∑ k : (dyadicLaw μ i).support,
    if normalizedDyadicEntropy (rescaledComponent μ i k)
      (rescaledComponent_hasBoundedSupport μ i k) m ≤ d - δ
      then ((dyadicLaw μ i) k).toReal else 0

theorem component_deviation_le_of_lower_tail (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) (m : ℕ) {d δ : ℝ}
    (hd : d ≤ 1) (hδ : 0 ≤ δ) (ε : ℝ) :
    ε * componentEntropyDeviationMass μ hμ i m d ε ≤
      averageComponentEntropy μ hμ i m - d + 2 * δ +
        2 * componentEntropyBelowMass μ hμ i m d δ := by
  classical
  let : Fintype (dyadicLaw μ i).support := (dyadicLaw_support_finite μ hμ i).fintype
  let H (k : (dyadicLaw μ i).support) : ℝ :=
    normalizedDyadicEntropy (rescaledComponent μ i k)
      (rescaledComponent_hasBoundedSupport μ i k) m
  have hpoint (k : (dyadicLaw μ i).support) :
      ε * (if ε ≤ |H k - d| then ((dyadicLaw μ i) k).toReal else 0) ≤
      ((dyadicLaw μ i) k).toReal * (H k - d + 2 * δ) +
        2 * (if H k ≤ d - δ then ((dyadicLaw μ i) k).toReal else 0) := by
    have hw : 0 ≤ ((dyadicLaw μ i) k).toReal := ENNReal.toReal_nonneg
    have hH : 0 ≤ H k := normalizedDyadicEntropy_nonneg _ _ _
    have habs : |H k - d| ≤ H k - d + 2 * δ +
        2 * (if H k ≤ d - δ then (1 : ℝ) else 0) := by
      split_ifs with hk <;> rw [abs_le] <;> constructor <;> simp only [mul_one, mul_zero] <;> linarith
    have hmul := mul_le_mul_of_nonneg_left habs hw
    split_ifs with he hk hk
    · have hε := mul_le_mul_of_nonneg_left he hw
      simp only [hk, ↓reduceIte] at hmul
      nlinarith
    · have hε := mul_le_mul_of_nonneg_left he hw
      simp only [hk, ↓reduceIte] at hmul
      nlinarith
    · simp only [hk, ↓reduceIte] at hmul
      nlinarith [mul_nonneg hw (abs_nonneg (H k - d))]
    · simp only [hk, ↓reduceIte] at hmul
      nlinarith [mul_nonneg hw (abs_nonneg (H k - d))]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun k _ ↦ hpoint k)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, mul_add, mul_sub,
    Finset.sum_sub_distrib, ← Finset.sum_mul, sum_dyadic_cell_mass μ hμ i,
    one_mul, Finset.sum_add_distrib] at hs
  exact hs

theorem level_deviation_le_of_uniform_lower_tail (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) {n : ℕ} (hn : 0 < n) (m : ℕ)
    {d δ : ℝ} (hd : d ≤ 1) (hδ : 0 ≤ δ) (ε : ℝ)
    (hlower : ∀ i : ℕ, componentEntropyBelowMass μ hμ i m d δ ≤ δ) :
    ε * levelEntropyDeviationMass μ hμ n m d ε ≤
      levelAverageComponentEntropy μ hμ n m - d + 4 * δ := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hs : (∑ i ∈ Finset.range n,
      ε * componentEntropyDeviationMass μ hμ i m d ε) ≤
      ∑ i ∈ Finset.range n, (averageComponentEntropy μ hμ i m - d + 4 * δ) := by
    apply Finset.sum_le_sum
    intro i _
    have h := component_deviation_le_of_lower_tail μ hμ i m hd hδ ε
    linarith [hlower i]
  have hdiv := div_le_div_of_nonneg_right hs hn'.le
  simpa only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, add_div, sub_div,
    mul_div_cancel_left₀ _ hn'.ne', mul_div_assoc,
    levelEntropyDeviationMass, levelAverageComponentEntropy] using hdiv

theorem hasUniformEntropyDimension_of_uniform_lower_tail (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) {d : ℝ} (hd : d ≤ 1)
    (hlim : Tendsto (normalizedDyadicEntropy μ hμ) atTop (𝓝 d))
    (hlower : ∀ δ : ℝ, 0 < δ → ∃ M : ℕ, ∀ m : ℕ, M ≤ m → 0 < m →
      ∀ i : ℕ, componentEntropyBelowMass μ hμ i m d δ ≤ δ) :
    HasUniformEntropyDimension μ hμ d := by
  intro ε hε
  let δ : ℝ := ε * ε / 16
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨M, hM⟩ := hlower δ hδ
  refine ⟨M, fun m hm hmpos ↦ ?_⟩
  have hmean := levelAverageComponentEntropy_tendsto μ hμ hlim hmpos
  have hgap : d < d + ε * ε / 2 := by nlinarith [mul_pos hε hε]
  filter_upwards [eventually_gt_atTop 0, hmean.eventually (gt_mem_nhds hgap)] with n hn hmean'
  have hdev := level_deviation_le_of_uniform_lower_tail μ hμ hn m hd hδ.le ε (hM m hm hmpos)
  have hsmall : ε * levelEntropyDeviationMass μ hμ n m d ε < ε * ε := by
    dsimp [δ] at hdev
    nlinarith [mul_pos hε hε]
  exact (mul_lt_mul_iff_right₀ hε).mp hsmall

end ExactOverlaps.Entropy
