module

public import ExactOverlaps.Probability.PositiveTriangleIntegral
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Translating the two halves of a cut-location integral

The isolated splitting point has zero Lebesgue measure. All statements use
nonnegative integrals, so they remain valid before proving finiteness.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ExactOverlaps.FiniteProbability

lemma lintegral_Ioi_sub_left (f : ℝ → ℝ≥0∞) (hf : Measurable f) (t : ℝ) :
    (∫⁻ u in Ioi (0 : ℝ), f (t - u)) = ∫⁻ a in Iio t, f a := by
  have hpre : (fun u : ℝ ↦ t - u) ⁻¹' Iio t = Ioi 0 := by
    ext u
    simp
  calc
    (∫⁻ u in Ioi (0 : ℝ), f (t - u)) =
        ∫⁻ a in Iio t, f a ∂volume.map (fun u : ℝ ↦ t - u) := by
      rw [setLIntegral_map measurableSet_Iio hf (by fun_prop), hpre]
    _ = _ := by rw [Measure.map_sub_left_eq_self]

lemma lintegral_eq_add_halflines (f : ℝ → ℝ≥0∞) (t : ℝ) :
    (∫⁻ a, f a) = (∫⁻ a in Iio t, f a) + ∫⁻ a in Ioi t, f a := by
  have h := lintegral_add_compl (μ := volume) f (A := Iio t) measurableSet_Iio
  rw [compl_Iio, Measure.restrict_congr_set (Ioi_ae_eq_Ici (μ := volume)).symm] at h
  exact h.symm

lemma lintegral_eq_translated_halflines (f : ℝ → ℝ≥0∞) (hf : Measurable f) (t : ℝ) :
    (∫⁻ a, f a) = (∫⁻ u in Ioi (0 : ℝ), f (t - u)) +
      ∫⁻ u in Ioi (0 : ℝ), f (t + u) := by
  rw [lintegral_Ioi_sub_left f hf t, Poisson.lintegral_Ioi_add f hf t]
  exact lintegral_eq_add_halflines f t

end ExactOverlaps.FiniteProbability
