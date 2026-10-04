module

public import ExactOverlaps.VarianceEnergy.Scaling

/-!
# Scale invariance of the full energy

The logarithmic measure `dr/r` cancels the positive change of scale. The
argument uses nonnegative integrals and therefore covers infinite energies.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace ExactOverlaps.VarianceEnergy

lemma lintegral_Ioi_div_pos (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    {u : ℝ} (hu : 0 < u) :
    (∫⁻ x in Ioi (0 : ℝ), f (x / u)) =
      ENNReal.ofReal u * ∫⁻ x in Ioi (0 : ℝ), f x := by
  have hpre : (fun x : ℝ ↦ x / u) ⁻¹' Ioi 0 = Ioi 0 := by
    ext x
    simp only [mem_preimage, mem_Ioi, div_pos_iff_of_pos_right hu]
  calc
    (∫⁻ x in Ioi (0 : ℝ), f (x / u)) =
        ∫⁻ x in Ioi (0 : ℝ), f x ∂volume.map (fun x : ℝ ↦ x / u) := by
      rw [setLIntegral_map measurableSet_Ioi hf (by fun_prop), hpre]
    _ = _ := by
      rw [map_volume_div_pos hu, Measure.restrict_smul, lintegral_smul_measure]
      rfl

lemma energy_map_mul_pos (μ : Measure ℝ) [IsFiniteMeasure μ] {u : ℝ} (hu : 0 < u) :
    energy (μ.map (fun x ↦ u * x)) = energy μ := by
  have hf : Measurable (fun r : ℝ ↦
      normalizedLocalVariance μ r * ENNReal.ofReal (1 / r)) :=
    (measurable_normalizedLocalVariance μ).mul (by fun_prop)
  have hfactor {r : ℝ} (hr : 0 < r) : ENNReal.ofReal (1 / r) =
      ENNReal.ofReal (1 / u) * ENNReal.ofReal (1 / (r / u)) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp [ne_of_gt hu, ne_of_gt hr]
  calc
    energy (μ.map (fun x ↦ u * x)) = ENNReal.ofReal (1 / u) *
        ∫⁻ r in Ioi (0 : ℝ),
          normalizedLocalVariance μ (r / u) * ENNReal.ofReal (1 / (r / u)) := by
      unfold energy
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      rw [normalizedLocalVariance_map_mul_pos μ hu hr, hfactor hr]
      ring
    _ = ENNReal.ofReal (1 / u) * (ENNReal.ofReal u * energy μ) := by
      rw [lintegral_Ioi_div_pos _ hf hu]
      rfl
    _ = energy μ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
        one_div_mul_cancel (ne_of_gt hu), ENNReal.ofReal_one, one_mul]

end ExactOverlaps.VarianceEnergy
