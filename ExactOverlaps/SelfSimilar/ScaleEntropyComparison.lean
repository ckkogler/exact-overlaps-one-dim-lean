module

public import ExactOverlaps.ScaleEntropy.Averaged
public import ExactOverlaps.SelfSimilar.AffineEntropy
public import ExactOverlaps.SelfSimilar.RatioLevels

/-!
Arbitrary positive meshes are compared with the nearest coarser dyadic level.
The comparison is uniform in the physical grid translation and therefore
survives averaging, including for laws with atoms on partition boundaries.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ExactOverlaps.ScaleEntropy

open Entropy SelfSimilar

noncomputable def meshSimilarity (i : ℤ) (r : ℝ) (hr : 0 < r) (t : ℝ) : RealSimilarity where
  ratio := ((2 : ℝ) ^ i * r)⁻¹
  ratio_ne_zero := inv_ne_zero (mul_ne_zero (zpow_ne_zero _ (by norm_num)) hr.ne')
  shift := t * ((2 : ℝ) ^ i * r)⁻¹

theorem dyadicQuantize_meshSimilarity (i : ℤ) (r : ℝ) (hr : 0 < r) (t x : ℝ) :
    dyadicQuantize i (meshSimilarity i r hr t x) = quantize r t x := by
  unfold dyadicQuantize quantize
  congr 1
  dsimp [meshSimilarity]
  field_simp [hr.ne', zpow_ne_zero i (by norm_num : (2 : ℝ) ≠ 0)]

theorem law_eq_dyadicLaw_meshSimilarity (μ : ProbabilityMeasure ℝ)
    (i : ℤ) (r : ℝ) (hr : 0 < r) (t : ℝ) :
    law μ r t = dyadicLaw (μ.map (meshSimilarity i r hr t)) i := by
  apply PMF.toMeasure_injective
  rw [law_toMeasure, dyadicLaw_toMeasure]
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (measurable_dyadicQuantize i) (meshSimilarity i r hr t).measurable]
  congr 1
  funext x
  exact (dyadicQuantize_meshSimilarity i r hr t x).symm

theorem abs_shiftedEntropy_sub_dyadicEntropy_le (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) (r : ℝ) (hr : 0 < r)
    (hlo : (1 : ℝ) / 2 ≤ (2 : ℝ) ^ i * r) (hhi : (2 : ℝ) ^ i * r ≤ 1) (t : ℝ) :
    |shiftedEntropy μ hμ r hr t - dyadicEntropy μ hμ i| ≤ Real.log 7 := by
  let g := meshSimilarity i r hr t
  have hA : 0 < (2 : ℝ) ^ i * r := mul_pos (zpow_pos (by norm_num) _) hr
  have hratio : |g.ratio| ≤ (2 : ℕ) := by
    dsimp [g, meshSimilarity]
    rw [abs_of_pos (inv_pos.mpr hA), inv_le_iff_one_le_mul₀ hA]
    linarith
  have hinverse : |g.ratio|⁻¹ ≤ (2 : ℕ) := by
    dsimp [g, meshSimilarity]
    rw [abs_of_pos (inv_pos.mpr hA), inv_inv]
    linarith
  have he : shiftedEntropy μ hμ r hr t =
      dyadicEntropy (μ.map g) (g.hasBoundedSupport_map μ hμ) i :=
    finiteEntropy_congr (law_eq_dyadicLaw_meshSimilarity μ i r hr t) _ _
  have hu := dyadicEntropy_map_affine_sub_le μ hμ g hratio i
  have hl := dyadicEntropy_le_map_affine_add μ hμ g hinverse i
  norm_num at hu hl
  rw [he, abs_le]
  constructor <;> linarith

theorem abs_entropy_sub_dyadicEntropy_le (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) (r : ℝ) (hr : 0 < r)
    (hlo : (1 : ℝ) / 2 ≤ (2 : ℝ) ^ i * r) (hhi : (2 : ℝ) ^ i * r ≤ 1) :
    |entropy μ hμ r hr - dyadicEntropy μ hμ i| ≤ Real.log 7 := by
  have hi := intervalIntegrable_shiftedEntropy μ hμ r hr 0 r
  have hb (t : ℝ) := abs_le.mp (abs_shiftedEntropy_sub_dyadicEntropy_le μ hμ i r hr hlo hhi t)
  have hl := intervalIntegral.integral_mono_on hr.le intervalIntegrable_const hi
    (fun t _ ↦ (show dyadicEntropy μ hμ i - Real.log 7 ≤ shiftedEntropy μ hμ r hr t by
      linarith [(hb t).1]))
  have hu := intervalIntegral.integral_mono_on hr.le hi intervalIntegrable_const
    (fun t _ ↦ (show shiftedEntropy μ hμ r hr t ≤ dyadicEntropy μ hμ i + Real.log 7 by
      linarith [(hb t).2]))
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hl hu
  have hlo' : dyadicEntropy μ hμ i - Real.log 7 ≤ entropy μ hμ r hr := by
    apply (le_div_iff₀ hr).mpr
    nlinarith [hl]
  have hhi' : entropy μ hμ r hr ≤ dyadicEntropy μ hμ i + Real.log 7 := by
    apply (div_le_iff₀ hr).mpr
    nlinarith [hu]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem abs_entropy_sub_ratioLevel_entropy_le (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (r : ℝ) (hr : 0 < r) :
    |entropy μ hμ r hr - dyadicEntropy μ hμ (ratioLevel r)| ≤ Real.log 7 := by
  apply abs_entropy_sub_dyadicEntropy_le μ hμ (ratioLevel r) r hr
  · simpa only [abs_of_pos hr] using (half_lt_ratioLevel_mul hr.ne').le
  · simpa only [abs_of_pos hr] using ratioLevel_mul_le_one hr.ne'

end ExactOverlaps.ScaleEntropy
