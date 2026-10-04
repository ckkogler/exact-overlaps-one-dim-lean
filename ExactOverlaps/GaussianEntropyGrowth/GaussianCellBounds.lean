/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.GaussianEntropyGrowth.MeshCells
public import ExactOverlaps.GaussianEntropyGrowth.Information
public import ExactOverlaps.GaussianScaleEntropy.GaussianMoments
public import ExactOverlaps.Entropy.GaussianDensity
public import ExactOverlaps.Entropy.DensityBounds

/-!
# Gaussian cell information at arbitrary mesh size

The Gaussian density ratio controls every point in the sampled cell.
Integrating the density over that cell compares its actual mass with the
mesh width times the density at the sample. Taking logarithms yields a
pointwise information error with an integrable first-moment bound.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ExactOverlaps.GaussianEntropyGrowth

open GaussianApproximation

def gaussianCellError (v : ℝ≥0) (r x : ℝ) : ℝ := (|x| + r) * r / (v : ℝ)

lemma gaussian_cell_mass_bounds (v : ℝ≥0) (hv : 0 < (v : ℝ))
    {r : ℝ} (hr : 0 < r) (t x : ℝ) :
    Real.exp (-gaussianCellError v r x) * gaussianPDFReal 0 v x * r ≤
      (ScaleEntropy.law (centeredGaussian v) r t (ScaleEntropy.quantize r t x)).toReal ∧
    (ScaleEntropy.law (centeredGaussian v) r t (ScaleEntropy.quantize r t x)).toReal ≤
      Real.exp (gaussianCellError v r x) * gaussianPDFReal 0 v x * r := by
  let k := ScaleEntropy.quantize r t x
  have hx : x ∈ meshCell r t k := mem_own_meshCell hr t x
  have hxR : |x - 0| ≤ |x| + r := by simp only [sub_zero]; linarith
  have hyR (y : ℝ) (hy : y ∈ meshCell r t k) : |y - 0| ≤ |x| + r := by
    have hd := abs_sub_le_of_mem_meshCell hy hx
    have ha := abs_add_le (y - x) x
    rw [sub_add_cancel] at ha
    simp only [sub_zero]
    linarith
  have hlow (y : ℝ) (hy : y ∈ meshCell r t k) :
      Real.exp (-gaussianCellError v r x) * gaussianPDFReal 0 v x ≤ gaussianPDFReal 0 v y :=
    Entropy.gaussianPDFReal_exp_neg_mul_le 0 v hv le_rfl (hyR y hy) hxR
      (abs_sub_le_of_mem_meshCell hy hx)
  have hupp (y : ℝ) (hy : y ∈ meshCell r t k) :
      gaussianPDFReal 0 v y ≤ Real.exp (gaussianCellError v r x) * gaussianPDFReal 0 v x :=
    Entropy.gaussianPDFReal_le_exp_mul 0 v hv le_rfl (hyR y hy) hxR
      (abs_sub_le_of_mem_meshCell hy hx)
  have hv0 : v ≠ 0 := by exact_mod_cast hv.ne'
  have hμ : (centeredGaussian v : Measure ℝ) =
      volume.withDensity (fun y ↦ ENNReal.ofReal (gaussianPDFReal 0 v y)) := by
    change gaussianReal 0 v = _
    exact gaussianReal_of_var_ne_zero 0 hv0
  have hl := Entropy.measure_ge_of_density_lower (centeredGaussian v) (gaussianPDFReal 0 v) hμ
    (measurableSet_meshCell r t k)
    (mul_nonneg (Real.exp_pos _).le (gaussianPDFReal_nonneg _ _ _)) hlow
  have hu := Entropy.measure_le_of_density_upper (centeredGaussian v) (gaussianPDFReal 0 v) hμ
    (measurableSet_meshCell r t k)
    (mul_nonneg (Real.exp_pos _).le (gaussianPDFReal_nonneg _ _ _)) hupp
    (by rw [volume_meshCell]; exact ENNReal.ofReal_ne_top)
  rw [volume_meshCell, ENNReal.toReal_ofReal hr.le] at hl hu
  rw [law_eq_meshCell_mass _ hr t]
  exact ⟨hl, hu⟩

lemma abs_gaussian_cellInformation_error (v : ℝ≥0) (hv : 0 < (v : ℝ))
    {r : ℝ} (hr : 0 < r) (t x : ℝ) :
    |cellInformation (centeredGaussian v) r t x + Real.log (gaussianPDFReal 0 v x) + Real.log r| ≤
      gaussianCellError v r x := by
  have hv0 : v ≠ 0 := by exact_mod_cast hv.ne'
  have hf : 0 < gaussianPDFReal 0 v x := gaussianPDFReal_pos 0 v x hv0
  obtain ⟨hl, hu⟩ := gaussian_cell_mass_bounds v hv hr t x
  have hp : 0 < (ScaleEntropy.law (centeredGaussian v) r t
      (ScaleEntropy.quantize r t x)).toReal :=
    (mul_pos (mul_pos (Real.exp_pos _) hf) hr).trans_le hl
  have hll := Real.log_le_log (mul_pos (mul_pos (Real.exp_pos _) hf) hr) hl
  have hlu := Real.log_le_log hp hu
  rw [Real.log_mul (mul_pos (Real.exp_pos _) hf).ne' hr.ne',
    Real.log_mul (Real.exp_pos _).ne' hf.ne', Real.log_exp] at hll hlu
  unfold cellInformation information
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end ExactOverlaps.GaussianEntropyGrowth
