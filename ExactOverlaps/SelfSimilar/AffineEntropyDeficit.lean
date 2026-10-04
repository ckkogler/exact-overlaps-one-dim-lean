module

public import ExactOverlaps.SelfSimilar.AffineUniformity
public import ExactOverlaps.Entropy.Uniformity

/-!
The quantitative entropy-deficit hypothesis for the inverse theorem follows
uniformly over signed affine normalizations from the standard dimension gap.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology BigOperators

namespace ExactOverlaps.Entropy

theorem one_sub_componentDeviation_le_lowerTail (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) (m : ℕ) {d ε a : ℝ}
    (hgap : d + ε ≤ 1 - a) :
    1 - componentEntropyDeviationMass μ hμ i m d ε ≤
      componentEntropyLowerTailMass μ hμ i m a := by
  classical
  let : Fintype (dyadicLaw μ i).support := (dyadicLaw_support_finite μ hμ i).fintype
  rw [← sum_dyadic_cell_mass μ hμ i]
  unfold componentEntropyDeviationMass componentEntropyLowerTailMass
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro k _
  split_ifs with hdev hlow hlow
  · simp
  · simp
  · simp
  · have hH : 1 - a < normalizedDyadicEntropy (rescaledComponent μ i k)
        (rescaledComponent_hasBoundedSupport μ i k) m := lt_of_not_ge hlow
    have habs := le_abs_self (normalizedDyadicEntropy (rescaledComponent μ i k)
      (rescaledComponent_hasBoundedSupport μ i k) m - d)
    exact False.elim (hdev (by linarith))

theorem one_sub_levelDeviation_le_lowerTail (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) {n : ℕ} (hn : 0 < n) (m : ℕ) {d ε a : ℝ}
    (hgap : d + ε ≤ 1 - a) :
    1 - levelEntropyDeviationMass μ hμ n m d ε ≤ levelEntropyLowerTailMass μ hμ n m a := by
  have h := Finset.sum_le_sum (s := Finset.range n)
    (fun i _ ↦ one_sub_componentDeviation_le_lowerTail μ hμ i m hgap)
  have hd := div_le_div_of_nonneg_right h (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  simpa only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one, sub_div, div_self (show (n : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr hn.ne'),
    levelEntropyDeviationMass, levelEntropyLowerTailMass] using hd

end ExactOverlaps.Entropy

namespace ExactOverlaps.SelfSimilar.System

open Entropy
variable {ι : Type*} [Fintype ι]

theorem uniform_affine_entropy_deficit (S : System ι) (μ : ProbabilityMeasure ℝ)
    (hμ : S.IsStationary (μ : Measure ℝ)) {a : ℝ} (ha : 0 < a) (K : ℕ)
    {b η : ℝ} (hgap : (lowerHausdorffDimension (μ : Measure ℝ)).toReal < 1 - b)
    (hη : 0 < η) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → 0 < m → ∀ᶠ n : ℕ in atTop,
      ∀ g : RealSimilarity, a ≤ |g.ratio| → |g.ratio| ≤ K →
        1 - η ≤ levelEntropyLowerTailMass (μ.map g)
          (g.hasBoundedSupport_map μ (S.hasBoundedSupport hμ)) n m b := by
  let d : ℝ := (lowerHausdorffDimension (μ : Measure ℝ)).toReal
  let ε : ℝ := min η ((1 - b - d) / 2)
  have hε : 0 < ε := lt_min hη (by dsimp [d]; linarith)
  have hεη : ε ≤ η := min_le_left _ _
  have hεgap : d + ε ≤ 1 - b := by
    have := min_le_right η ((1 - b - d) / 2)
    dsimp [ε]
    dsimp [d] at *
    linarith
  obtain ⟨M, hM⟩ := S.uniform_affine_entropy_dimension μ hμ ha K hε
  refine ⟨M, fun m hm hmpos ↦ ?_⟩
  filter_upwards [eventually_gt_atTop 0, hM m hm hmpos] with n hn hcon
  intro g hga hgK
  have hdev := hcon g hga hgK
  have htail := one_sub_levelDeviation_le_lowerTail (μ.map g)
    (g.hasBoundedSupport_map μ (S.hasBoundedSupport hμ)) hn m hεgap
  dsimp [d] at htail
  linarith

end ExactOverlaps.SelfSimilar.System
