module

public import ExactOverlaps.EntropyEnergyGap.ConditionalEnergy
public import ExactOverlaps.EntropyEnergyGap.FiberAverages
public import ExactOverlaps.ScaleEntropy.Basic
public import ExactOverlaps.VarianceEnergy.Diameter

/-!
# The exact half-unit energy tail in a mesh cell

A quantizer fiber lies in its actual half-open interval of length R. Its
finite-law energy above scale R is at most one half. Conditional Jensen
therefore bounds the mean full conditional energy by the original energy
below R plus one half.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal Classical
open ExactOverlaps.Entropy ExactOverlaps.VarianceEnergy ExactOverlaps.FiniteProbability
open ExactOverlaps.ScaleEntropy

namespace ExactOverlaps.EntropyEnergyGap

lemma finiteLaw_ae_mem_support (p : PMF ℝ) (hp : p.support.Finite) :
    ∀ᵐ x ∂p.toMeasure, x ∈ hp.toFinset := by
  rw [ae_iff]
  change p.toMeasure ((hp.toFinset : Set ℝ)ᶜ) = 0
  apply (p.toMeasure_apply_eq_zero_iff hp.toFinset.measurableSet.compl).mpr
  apply Set.disjoint_left.mpr
  intro a ha hb
  exact hb (by simpa using ha)

lemma mem_quantizer_cell {R t x : ℝ} (hR : 0 < R) (b : ℤ)
    (hx : quantize R t x = b) : x ∈ Ico (R * b - t) (R * b - t + R) := by
  have h := Int.floor_eq_iff.mp hx
  rw [le_div_iff₀ hR, div_lt_iff₀ hR] at h
  constructor <;> nlinarith [h.1, h.2]

lemma quantized_conditional_energy_tail_le (p : PMF ℝ) (hp : p.support.Finite)
    {R : ℝ} (hR : 0 < R) (t : ℝ) (b : (p.map (quantize R t)).support) :
    (energy (conditionalPMF p (quantize R t) b).toMeasure).toReal ≤
      (energyBelow (conditionalPMF p (quantize R t) b).toMeasure R).toReal + 1 / 2 := by
  let q := conditionalPMF p (quantize R t) b
  have hq : q.support.Finite := conditionalPMF_support_finite p hp _ b
  have hs : ∀ᵐ x ∂q.toMeasure, x ∈ hq.toFinset := finiteLaw_ae_mem_support q hq
  have hcell : ∀ᵐ x ∂q.toMeasure, x ∈ Icc (R * b.val - t) (R * b.val - t + R) := by
    filter_upwards [hs] with x hx
    have hx' : x ∈ q.support := by simpa using hx
    rw [conditionalPMF_support] at hx'
    exact ⟨(mem_quantizer_cell hR b hx'.1).1, (mem_quantizer_cell hR b hx'.1).2.le⟩
  have h := energy_toReal_sub_energyBelow_le q.toMeasure hq.toFinset hs hcell hR
  have he : R ^ 2 / (2 * R ^ 2) = (1 : ℝ) / 2 := by field_simp
  rw [he] at h
  linarith

theorem mean_quantized_energy_le (p : PMF ℝ) (hp : p.support.Finite)
    {R : ℝ} (hR : 0 < R) (t : ℝ) :
    meanFiberFunctional p hp (quantize R t) (fun q _ ↦ (energy q.toMeasure).toReal) ≤
      (energyBelow p.toMeasure R).toReal + 1 / 2 := by
  have h := meanFiberFunctional_mono p hp (quantize R t)
    (fun q _ ↦ (energy q.toMeasure).toReal)
    (fun q _ ↦ (energyBelow q.toMeasure R).toReal + 1 / 2)
    (quantized_conditional_energy_tail_le p hp hR t)
  rw [meanFiberFunctional_add_const] at h
  exact h.trans (add_le_add (mean_conditional_energyBelow_le p hp (quantize R t) R) le_rfl)

end ExactOverlaps.EntropyEnergyGap
