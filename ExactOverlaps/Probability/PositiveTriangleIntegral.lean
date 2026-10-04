module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-!
# Tonelli's identity for positive refinement times

Integrating a nonnegative function of `t+u` over two positive times gives
its first moment. No integrability or finiteness assumption is needed.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ExactOverlaps.Poisson

lemma lintegral_Ioi_add (f : ℝ → ℝ≥0∞) (hf : Measurable f) (t : ℝ) :
    (∫⁻ u in Ioi (0 : ℝ), f (t + u)) = ∫⁻ s in Ioi t, f s := by
  have hpre : (fun u : ℝ ↦ t + u) ⁻¹' Ioi t = Ioi 0 := by
    ext u
    simp
  calc
    (∫⁻ u in Ioi (0 : ℝ), f (t + u)) =
        ∫⁻ s in Ioi t, f s ∂volume.map (fun u : ℝ ↦ t + u) := by
      rw [setLIntegral_map measurableSet_Ioi hf (by fun_prop), hpre]
    _ = _ := by rw [map_add_left_eq_self]

lemma lintegral_positive_triangle (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ t in Ioi (0 : ℝ), ∫⁻ u in Ioi (0 : ℝ), f (t + u)) =
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal s * f s := by
  classical
  let g : ℝ → ℝ → ℝ≥0∞ := fun t s ↦ if t < s then f s else 0
  have hg : Measurable (Function.uncurry g) := by
    exact Measurable.ite (measurableSet_lt measurable_fst measurable_snd)
      (hf.comp measurable_snd) measurable_const
  have htail (t : ℝ) : (∫⁻ s, g t s) = ∫⁻ s in Ioi t, f s := by
    change (∫⁻ s, (Ioi t).indicator f s) = _
    exact lintegral_indicator measurableSet_Ioi f
  have hinner (s : ℝ) : (∫⁻ t in Ioi (0 : ℝ), g t s) = ENNReal.ofReal s * f s := by
    change (∫⁻ t in Ioi (0 : ℝ), (Iio s).indicator (fun _ ↦ f s) t) = _
    rw [lintegral_indicator measurableSet_Iio]
    have he : Iio s ∩ Ioi (0 : ℝ) = Ioo 0 s := by
      ext t
      simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_Ioo]
      exact and_comm
    simp [Measure.restrict_apply, measurableSet_Iio, he, Real.volume_Ioo, mul_comm]
  calc
    (∫⁻ t in Ioi (0 : ℝ), ∫⁻ u in Ioi (0 : ℝ), f (t + u)) =
        ∫⁻ t in Ioi (0 : ℝ), ∫⁻ s, g t s := by
      simp_rw [lintegral_Ioi_add f hf, htail]
    _ = ∫⁻ s, ∫⁻ t in Ioi (0 : ℝ), g t s := lintegral_lintegral_swap hg.aemeasurable
    _ = ∫⁻ s, ENNReal.ofReal s * f s := by simp_rw [hinner]
    _ = ∫⁻ s, (Ioi (0 : ℝ)).indicator (fun s ↦ ENNReal.ofReal s * f s) s := by
      apply lintegral_congr
      intro s
      by_cases hs : 0 < s
      · simp [hs]
      · simp [hs, ENNReal.ofReal_eq_zero.mpr (le_of_not_gt hs)]
    _ = _ := lintegral_indicator measurableSet_Ioi _

end ExactOverlaps.Poisson
