/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.GaussianScaleEntropy.Basic

/-! # Exact geometry and masses of arbitrary positive mesh cells -/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace ExactOverlaps.GaussianEntropyGrowth

def meshCell (r t : ℝ) (k : ℤ) : Set ℝ := Ico (r * k - t) (r * k - t + r)

lemma measurableSet_meshCell (r t : ℝ) (k : ℤ) : MeasurableSet (meshCell r t k) :=
  measurableSet_Ico

lemma quantize_eq_iff_mem_meshCell {r : ℝ} (hr : 0 < r) (t x : ℝ) (k : ℤ) :
    ScaleEntropy.quantize r t x = k ↔ x ∈ meshCell r t k := by
  unfold ScaleEntropy.quantize meshCell
  rw [Int.floor_eq_iff, le_div_iff₀ hr, div_lt_iff₀ hr]
  constructor <;> intro h <;> constructor <;> nlinarith [h.1, h.2]

lemma mem_own_meshCell {r : ℝ} (hr : 0 < r) (t x : ℝ) :
    x ∈ meshCell r t (ScaleEntropy.quantize r t x) :=
  (quantize_eq_iff_mem_meshCell hr t x _).mp rfl

lemma abs_sub_le_of_mem_meshCell {r t x y : ℝ} {k : ℤ}
    (hx : x ∈ meshCell r t k) (hy : y ∈ meshCell r t k) : |x - y| ≤ r := by
  apply abs_le.mpr
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

lemma volume_meshCell (r t : ℝ) (k : ℤ) : volume (meshCell r t k) = ENNReal.ofReal r := by
  rw [meshCell, Real.volume_Ico]
  congr 1
  ring

lemma law_eq_meshCell_mass (μ : ProbabilityMeasure ℝ) {r : ℝ} (hr : 0 < r)
    (t : ℝ) (k : ℤ) : ScaleEntropy.law μ r t k = (μ : Measure ℝ) (meshCell r t k) := by
  rw [ScaleEntropy.law_apply]
  congr 1
  ext x
  exact quantize_eq_iff_mem_meshCell hr t x k

end ExactOverlaps.GaussianEntropyGrowth
