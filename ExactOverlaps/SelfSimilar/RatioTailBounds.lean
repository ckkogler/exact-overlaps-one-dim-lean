module

public import ExactOverlaps.SelfSimilar.RatioComponents
public import ExactOverlaps.SelfSimilar.RatioLevelConcentration
public import ExactOverlaps.SelfSimilar.AffineEntropyLimit

/-! Uniform entropy bounds for the actual signed ratio-class tails. -/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology BigOperators Classical

namespace ExactOverlaps.SelfSimilar.System

open Entropy
variable {ι : Type*} [Fintype ι]

theorem wordRatioLaw_support_abs_le_one (S : System ι) (n : ℕ)
    (r : (S.wordRatioLaw n).support) : |(r : ℝ)| ≤ 1 := by
  obtain ⟨w, _, hw⟩ := (PMF.mem_support_map_iff _ _ _).mp r.property
  rw [← hw]
  simpa only [one_pow] using S.abs_wordRatio_le_pow (by norm_num : (0 : ℝ) ≤ 1)
    (fun i ↦ (S.contracting i).le) n w

theorem ratioScaledEntropy_le (S : System ι) (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (n : ℕ) (r : (S.wordRatioLaw n).support) (i : ℤ) :
    dyadicEntropy (S.ratioScaledProbability μ n r)
        (S.ratioScaledProbability_hasBoundedSupport μ hμ n r) i ≤
      dyadicEntropy μ hμ i + Real.log 5 := by
  have h := dyadicEntropy_map_affine_sub_le μ hμ (S.ratioDilation n r)
    (K := 1) (by simpa only [ratioDilation, Nat.cast_one] using
      S.wordRatioLaw_support_abs_le_one n r) i
  norm_num only [Nat.cast_one, mul_one, show (2 : ℝ) + 3 = 5 by norm_num] at h
  change dyadicEntropy (S.ratioScaledProbability μ n r) _ i - dyadicEntropy μ hμ i ≤ _ at h
  linarith

theorem ratioScaledEntropy_at_ratioLevel_le (S : System ι) (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (n : ℕ) (r : (S.wordRatioLaw n).support) :
    dyadicEntropy (S.ratioScaledProbability μ n r)
        (S.ratioScaledProbability_hasBoundedSupport μ hμ n r) (ratioLevel r) ≤
      dyadicEntropy μ hμ 0 + Real.log 5 := by
  let g := (S.ratioDilation n r).dyadicScale (ratioLevel r)
  have hg : |g.ratio| ≤ (1 : ℕ) := by
    simp only [g, RealSimilarity.dyadicScale, ratioDilation, Nat.cast_one]
    rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) _)]
    exact ratioLevel_mul_le_one (S.wordRatioLaw_support_ne_zero n r)
  have h := dyadicEntropy_map_affine_sub_le μ hμ g hg 0
  change dyadicEntropy (μ.map ((S.ratioDilation n r).dyadicScale (ratioLevel r))) _ 0 -
    dyadicEntropy μ hμ 0 ≤ Real.log (2 * (1 : ℕ) + 3 : ℝ) at h
  rw [dyadicEntropy_affine_scale μ hμ (S.ratioDilation n r) (ratioLevel r) 0, add_zero] at h
  simp only [Nat.cast_one, mul_one] at h
  norm_num only [show (2 : ℝ) + 3 = 5 by norm_num] at h
  change dyadicEntropy (S.ratioScaledProbability μ n r) _ (ratioLevel r) -
    dyadicEntropy μ hμ 0 ≤ Real.log 5 at h
  linarith

theorem ratioScaledEntropy_below_ratioLevel_le (S : System ι) (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (n : ℕ) (r : (S.wordRatioLaw n).support) {i : ℤ}
    (hi : i ≤ ratioLevel r) :
    dyadicEntropy (S.ratioScaledProbability μ n r)
        (S.ratioScaledProbability_hasBoundedSupport μ hμ n r) i ≤
      dyadicEntropy μ hμ 0 + Real.log 5 :=
  (dyadicEntropy_mono _ _ hi).trans (S.ratioScaledEntropy_at_ratioLevel_le μ hμ n r)

theorem averageRatioScaledEntropy_nonneg (S : System ι) (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (n : ℕ) (i : ℤ) :
    0 ≤ S.averageRatioScaledEntropy μ hμ n i := by
  classical
  exact Finset.sum_nonneg (fun r _ ↦ mul_nonneg ENNReal.toReal_nonneg (dyadicEntropy_nonneg _ _ _))

/-- Split the exact class average into a uniformly bounded good part and its exceptional mass. -/
theorem averageRatioScaledEntropy_le_split (S : System ι) (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (n : ℕ) (i : ℤ) (E : Set ℝ) (hE : MeasurableSet E)
    {C B : ℝ} (hC : 0 ≤ C)
    (hgood : ∀ r : (S.wordRatioLaw n).support, (r : ℝ) ∉ E →
      dyadicEntropy (S.ratioScaledProbability μ n r)
        (S.ratioScaledProbability_hasBoundedSupport μ hμ n r) i ≤ C)
    (hall : ∀ r : (S.wordRatioLaw n).support,
      dyadicEntropy (S.ratioScaledProbability μ n r)
        (S.ratioScaledProbability_hasBoundedSupport μ hμ n r) i ≤ B) :
    S.averageRatioScaledEntropy μ hμ n i ≤ C +
      B * ((S.wordRatioLaw n).toMeasure E).toReal := by
  let : Fintype (S.wordRatioLaw n).support := (S.wordRatioLaw_support_finite n).fintype
  let p := supportLaw (S.wordRatioLaw n)
  have h := Finset.sum_le_sum (s := Finset.univ) (fun r _ ↦ show
      (p r).toReal * dyadicEntropy (S.ratioScaledProbability μ n r)
        (S.ratioScaledProbability_hasBoundedSupport μ hμ n r) i ≤
      (p r).toReal * C + B * (if (r : ℝ) ∈ E then (p r).toReal else 0) from by
    have hw : 0 ≤ (p r).toReal := ENNReal.toReal_nonneg
    by_cases hr : (r : ℝ) ∈ E
    · simp only [ite_eq_left hr]
      have hb := mul_le_mul_of_nonneg_left (hall r) hw
      have hc := mul_nonneg hw hC
      nlinarith
    · simp only [ite_eq_right hr, mul_zero, add_zero]
      exact mul_le_mul_of_nonneg_left (hgood r hr) hw)
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    sum_pmf_toReal, one_mul] at h
  rw [S.wordRatioLaw_mass_eq_support_sum n E hE]
  simpa only [p, supportLaw_apply, averageRatioScaledEntropy] using h

end ExactOverlaps.SelfSimilar.System
