module

public import ExactOverlaps.Entropy.Atomicity
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
Uniform entropy dimension is a concentration statement about actual
rescaled dyadic components, averaged over levels. The zero-dimensional
case follows from entropy averaging and Markov's inequality for every
bounded probability measure whose entropy dimension is zero.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology ENNReal BigOperators

namespace ExactOverlaps.Entropy

/-- Mass of components whose normalized entropy differs from `d` by at least `ε`. -/
noncomputable def componentEntropyDeviationMass (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) (m : ℕ) (d ε : ℝ) : ℝ := by
  classical
  letI : Fintype (dyadicLaw μ i).support := (dyadicLaw_support_finite μ hμ i).fintype
  exact ∑ k : (dyadicLaw μ i).support,
    if ε ≤ |normalizedDyadicEntropy (rescaledComponent μ i k)
      (rescaledComponent_hasBoundedSupport μ i k) m - d|
      then ((dyadicLaw μ i) k).toReal else 0

/-- The level is sampled uniformly from `0,…,n−1`, then the point by its actual law. -/
noncomputable def levelEntropyDeviationMass (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (n m : ℕ) (d ε : ℝ) : ℝ :=
  (∑ i ∈ Finset.range n, componentEntropyDeviationMass μ hμ i m d ε) / n

/-- For every tolerance, all sufficiently long component windows concentrate
around `d` when the number of sampled levels tends to infinity. -/
def HasUniformEntropyDimension (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (d : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m : ℕ, M ≤ m → 0 < m →
    ∀ᶠ n : ℕ in atTop, levelEntropyDeviationMass μ hμ n m d ε < ε

theorem componentEntropyDeviationMass_nonneg (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) (m : ℕ) (d ε : ℝ) :
    0 ≤ componentEntropyDeviationMass μ hμ i m d ε := by
  unfold componentEntropyDeviationMass
  apply Finset.sum_nonneg
  intro k _
  split_ifs <;> positivity

theorem componentEntropyDeviationMass_le_one (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) (m : ℕ) (d ε : ℝ) :
    componentEntropyDeviationMass μ hμ i m d ε ≤ 1 := by
  let : Fintype (dyadicLaw μ i).support := (dyadicLaw_support_finite μ hμ i).fintype
  rw [← sum_dyadic_cell_mass μ hμ i]
  unfold componentEntropyDeviationMass
  apply Finset.sum_le_sum
  intro k _
  split_ifs <;> simp

theorem componentEntropyDeviationMass_zero_dimension (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) (m : ℕ) (ε : ℝ) :
    componentEntropyDeviationMass μ hμ i m 0 ε = componentEntropyTailMass μ hμ i m ε := by
  unfold componentEntropyDeviationMass componentEntropyTailMass
  simp only [sub_zero, abs_of_nonneg (normalizedDyadicEntropy_nonneg _ _ _)]

theorem levelEntropyDeviationMass_zero_dimension (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (n m : ℕ) (ε : ℝ) :
    levelEntropyDeviationMass μ hμ n m 0 ε = levelEntropyTailMass μ hμ n m ε := by
  simp only [levelEntropyDeviationMass, componentEntropyDeviationMass_zero_dimension,
    levelEntropyTailMass]

theorem levelAverageComponentEntropy_tendsto (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) {d : ℝ}
    (hd : Tendsto (normalizedDyadicEntropy μ hμ) atTop (𝓝 d))
    {m : ℕ} (hm : 0 < m) :
    Tendsto (fun n : ℕ ↦ levelAverageComponentEntropy μ hμ n m) atTop (𝓝 d) := by
  have herr : Tendsto (fun n : ℕ ↦ levelAverageComponentEntropy μ hμ n m -
      normalizedDyadicEntropy μ hμ n) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simp only [Real.norm_eq_abs]
    have hbound : Tendsto (fun n : ℕ ↦ (m : ℝ) / n +
        dyadicEntropy μ hμ 0 / ((n : ℝ) * Real.log 2)) atTop (𝓝 0) := by
      have h := (tendsto_const_div_atTop_nhds_zero_nat (m : ℝ)).add
        (tendsto_const_div_atTop_nhds_zero_nat (dyadicEntropy μ hμ 0 / Real.log 2))
      have he : (fun n : ℕ ↦ (m : ℝ) / n +
          dyadicEntropy μ hμ 0 / ((n : ℝ) * Real.log 2)) =
          (fun n : ℕ ↦ (m : ℝ) / n + (dyadicEntropy μ hμ 0 / Real.log 2) / n) := by
        funext n
        ring
      rw [he]
      simpa only [zero_add] using h
    apply squeeze_zero' (Eventually.of_forall fun n ↦ abs_nonneg _) _ hbound
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact abs_levelAverageComponentEntropy_sub_le μ hμ hn hm
  simpa only [sub_add_cancel, zero_add] using herr.add hd

theorem hasUniformEntropyDimension_zero (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ)
    (hzero : Tendsto (normalizedDyadicEntropy μ hμ) atTop (𝓝 0)) :
    HasUniformEntropyDimension μ hμ 0 := by
  intro ε hε
  refine ⟨1, fun m _ hm ↦ ?_⟩
  have hmean := levelAverageComponentEntropy_tendsto μ hμ hzero hm
  filter_upwards [hmean.eventually (gt_mem_nhds (mul_pos hε hε))] with n hn
  rw [levelEntropyDeviationMass_zero_dimension]
  have hmarkov := mul_levelEntropyTailMass_le μ hμ n m ε
  exact (mul_lt_mul_iff_right₀ hε).mp (hmarkov.trans_lt hn)

end ExactOverlaps.Entropy
