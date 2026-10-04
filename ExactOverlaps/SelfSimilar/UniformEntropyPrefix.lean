module

public import ExactOverlaps.SelfSimilar.UniformEntropyCriterion

/-! A finite initial set of unresolved levels has a vanishing cost in entropy concentration. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators

namespace ExactOverlaps.Entropy

theorem componentEntropyBelowMass_le_one (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) (m : ℕ) (d δ : ℝ) :
    componentEntropyBelowMass μ hμ i m d δ ≤ 1 := by
  classical
  let : Fintype (dyadicLaw μ i).support := (dyadicLaw_support_finite μ hμ i).fintype
  rw [← sum_dyadic_cell_mass μ hμ i]
  unfold componentEntropyBelowMass
  apply Finset.sum_le_sum
  intro k _
  split_ifs <;> simp

theorem level_deviation_le_of_eventual_lower_tail (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) {n L : ℕ} (hn : 0 < n) (hL : L ≤ n) (m : ℕ)
    {d δ : ℝ} (hd : d ≤ 1) (hδ : 0 ≤ δ) (ε : ℝ)
    (hlower : ∀ i : ℕ, L ≤ i → componentEntropyBelowMass μ hμ i m d δ ≤ δ) :
    ε * levelEntropyDeviationMass μ hμ n m d ε ≤
      levelAverageComponentEntropy μ hμ n m - d + 4 * δ + 2 * (L : ℝ) / n := by
  classical
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hpoint (i : ℕ) :
      ε * componentEntropyDeviationMass μ hμ i m d ε ≤
        averageComponentEntropy μ hμ i m - d + 4 * δ + (if i < L then 2 else 0) := by
    have h := component_deviation_le_of_lower_tail μ hμ i m hd hδ ε
    split_ifs with hi
    · linarith [componentEntropyBelowMass_le_one μ hμ i m d δ]
    · have := hlower i (Nat.le_of_not_gt hi)
      linarith
  have hcount : (∑ i ∈ Finset.range n, if i < L then (2 : ℝ) else 0) = 2 * L := by
    rw [← Finset.sum_filter]
    have he : (Finset.range n).filter (fun i ↦ i < L) = Finset.range L := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [he]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hs := Finset.sum_le_sum (s := Finset.range n) (fun i _ ↦ hpoint i)
  simp only [Finset.sum_add_distrib, hcount, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum] at hs
  have hdiv := div_le_div_of_nonneg_right hs hn'.le
  simpa only [add_div, sub_div, mul_div_cancel_left₀ _ hn'.ne', mul_div_assoc,
    levelEntropyDeviationMass, levelAverageComponentEntropy] using hdiv

end ExactOverlaps.Entropy
