module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
Distribution-function comparison under a bounded-displacement coupling,
and continuity of distribution functions through shrinking geometric
right neighborhoods. These facts give uniqueness of stationary laws.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

namespace ExactOverlaps

theorem coupling_snd_Iic_le_fst (P : ProbabilityMeasure (ℝ × ℝ)) {δ : ℝ}
    (hδ : ∀ᵐ z ∂(P : Measure (ℝ × ℝ)), |z.2 - z.1| ≤ δ) (x : ℝ) :
    (P.map Prod.snd : Measure ℝ) (Iic x) ≤ (P.map Prod.fst : Measure ℝ) (Iic (x + δ)) := by
  rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply measurable_snd measurableSet_Iic,
    Measure.map_apply measurable_fst measurableSet_Iic]
  apply measure_mono_ae
  filter_upwards [hδ] with z hz
  intro hx
  change z.1 ≤ x + δ
  change z.2 ≤ x at hx
  have h := (abs_le.mp hz).1
  linarith

theorem coupling_fst_Iic_le_snd (P : ProbabilityMeasure (ℝ × ℝ)) {δ : ℝ}
    (hδ : ∀ᵐ z ∂(P : Measure (ℝ × ℝ)), |z.2 - z.1| ≤ δ) (x : ℝ) :
    (P.map Prod.fst : Measure ℝ) (Iic x) ≤ (P.map Prod.snd : Measure ℝ) (Iic (x + δ)) := by
  rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply measurable_fst measurableSet_Iic,
    Measure.map_apply measurable_snd measurableSet_Iic]
  apply measure_mono_ae
  filter_upwards [hδ] with z hz
  intro hx
  change z.2 ≤ x + δ
  change z.1 ≤ x at hx
  have h := (abs_le.mp hz).2
  linarith

theorem measure_Iic_eq_iInf_geometric (μ : Measure ℝ) [IsFiniteMeasure μ]
    {c R : ℝ} (hc : 0 ≤ c) (hc1 : c < 1) (hR : 0 ≤ R) (x : ℝ) :
    μ (Iic x) = ⨅ n : ℕ, μ (Iic (x + c ^ n * R)) := by
  have hanti : Antitone (fun n : ℕ ↦ Iic (x + c ^ n * R)) := by
    apply antitone_nat_of_succ_le
    intro n
    apply Iic_subset_Iic.2
    rw [pow_succ]
    have hn := pow_nonneg hc n
    nlinarith [mul_nonneg hn hR]
  have heq : Iic x = ⋂ n : ℕ, Iic (x + c ^ n * R) := by
    ext y
    simp only [mem_Iic, mem_iInter]
    constructor
    · intro hy n
      exact hy.trans (le_add_of_nonneg_right (mul_nonneg (pow_nonneg hc n) hR))
    · intro hy
      have ht : Tendsto (fun n : ℕ ↦ x + c ^ n * R) atTop (𝓝 x) := by
        simpa using tendsto_const_nhds.add
          ((tendsto_pow_atTop_nhds_zero_of_lt_one hc hc1).mul_const R)
      exact le_of_tendsto_of_tendsto' tendsto_const_nhds ht hy
  rw [heq]
  exact hanti.measure_iInter (fun _ ↦ measurableSet_Iic.nullMeasurableSet)
    ⟨0, measure_ne_top _ _⟩

end ExactOverlaps
