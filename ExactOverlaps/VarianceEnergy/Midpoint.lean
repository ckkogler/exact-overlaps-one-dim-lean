module

public import ExactOverlaps.VarianceEnergy.Basic
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# The local midpoint bound

The midpoint of a window of length `r` bounds the squared error by `r²/4`.
This is the pointwise input for normalization of local variance in Lemma 2.1.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace ExactOverlaps.VarianceEnergy

lemma sq_sub_midpoint_le {a r x : ℝ} (hx : x ∈ Ico a (a + r)) :
    (x - (a + r / 2)) ^ 2 ≤ r ^ 2 / 4 := by
  have hleft : -(r / 2) ≤ x - (a + r / 2) := by linarith [hx.1]
  have hright : x - (a + r / 2) ≤ r / 2 := by linarith [hx.2]
  nlinarith [mul_nonneg (sub_nonneg.mpr hleft) (sub_nonneg.mpr hright)]

lemma localQuadraticError_midpoint_le (μ : Measure ℝ) (a r : ℝ) :
    localQuadraticError μ a r (a + r / 2) ≤
      ENNReal.ofReal (r ^ 2 / 4) * μ (Ico a (a + r)) := by
  calc
    localQuadraticError μ a r (a + r / 2) ≤
        ∫⁻ _ in Ico a (a + r), ENNReal.ofReal (r ^ 2 / 4) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
      exact ENNReal.ofReal_le_ofReal (sq_sub_midpoint_le hx)
    _ = _ := by simp

lemma localVarianceMass_midpoint_le (μ : Measure ℝ) (a r : ℝ) :
    localVarianceMass μ a r ≤ ENNReal.ofReal (r ^ 2 / 4) * μ (Ico a (a + r)) :=
  (localVarianceMass_le μ a r (a + r / 2)).trans
    (localQuadraticError_midpoint_le μ a r)

@[simp] lemma localVarianceMass_dirac (x a r : ℝ) :
    localVarianceMass (Measure.dirac x) a r = 0 := by
  classical
  apply le_antisymm _ zero_le
  apply (localVarianceMass_le (Measure.dirac x) a r x).trans
  by_cases hx : x ∈ Ico a (a + r)
  · simp [localQuadraticError, restrict_dirac, hx]
  · simp [localQuadraticError, restrict_dirac, hx]

end ExactOverlaps.VarianceEnergy
