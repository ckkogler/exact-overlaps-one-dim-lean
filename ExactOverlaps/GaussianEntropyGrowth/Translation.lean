/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.GaussianScaleEntropy.Basic

/-! # Translation invariance of physical scale entropy for bounded laws -/

@[expose] public section

noncomputable section
open MeasureTheory Set

namespace ExactOverlaps.GaussianEntropyGrowth

def translate (μ : ProbabilityMeasure ℝ) (b : ℝ) : ProbabilityMeasure ℝ :=
  μ.map (fun x ↦ x + b)

lemma translate_hasBoundedSupport (μ : ProbabilityMeasure ℝ)
    (hμ : Entropy.HasBoundedSupport μ) (b : ℝ) : Entropy.HasBoundedSupport (translate μ b) := by
  obtain ⟨u, v, huv⟩ := hμ
  refine ⟨u + b, v + b, ?_⟩
  change ∀ᵐ x ∂((μ : Measure ℝ).map (fun x ↦ x + b)), x ∈ Icc (u + b) (v + b)
  apply (ae_map_iff (by fun_prop) measurableSet_Icc).mpr
  filter_upwards [huv] with x hx
  exact ⟨add_le_add hx.1 le_rfl, add_le_add hx.2 le_rfl⟩

lemma law_translate (μ : ProbabilityMeasure ℝ) (b r t : ℝ) :
    ScaleEntropy.law (translate μ b) r t = ScaleEntropy.law μ r (t + b) := by
  have hm : Measurable (fun x : ℝ ↦ x + b) := by fun_prop
  apply PMF.toMeasure_injective
  rw [ScaleEntropy.law_toMeasure, ScaleEntropy.law_toMeasure, translate,
    ProbabilityMeasure.toMeasure_map, Measure.map_map (ScaleEntropy.measurable_quantize r t) hm]
  congr 1
  funext x
  change ScaleEntropy.quantize r t (x + b) = ScaleEntropy.quantize r (t + b) x
  unfold ScaleEntropy.quantize
  congr 2
  ring

lemma shiftedEntropy_translate (μ : ProbabilityMeasure ℝ) (b r t : ℝ) :
    GaussianScaleEntropy.shiftedEntropy (translate μ b) r t =
      GaussianScaleEntropy.shiftedEntropy μ r (t + b) := by
  simp only [GaussianScaleEntropy.shiftedEntropy, GaussianScaleEntropy.cellEntropy,
    GaussianScaleEntropy.cellTerm, law_translate]

theorem entropy_translate (μ : ProbabilityMeasure ℝ)
    (hμ : Entropy.HasBoundedSupport μ) (b : ℝ) {r : ℝ} (hr : 0 < r) :
    GaussianScaleEntropy.entropy (translate μ b) r = GaussianScaleEntropy.entropy μ r := by
  rw [GaussianScaleEntropy.entropy_eq_bounded μ hμ hr]
  unfold GaussianScaleEntropy.entropy
  simp_rw [shiftedEntropy_translate, GaussianScaleEntropy.shiftedEntropy_eq_bounded μ hμ hr]
  rw [intervalIntegral.integral_comp_add_right]
  simpa only [zero_add, add_comm r b] using
    (ScaleEntropy.entropy_eq_average_from μ hμ r hr b).symm

theorem entropyBetween_translate (μ : ProbabilityMeasure ℝ)
    (hμ : Entropy.HasBoundedSupport μ) (b : ℝ) {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    GaussianScaleEntropy.entropyBetween (translate μ b) r R =
      GaussianScaleEntropy.entropyBetween μ r R := by
  simp only [GaussianScaleEntropy.entropyBetween, entropy_translate μ hμ b hr,
    entropy_translate μ hμ b hR]

end ExactOverlaps.GaussianEntropyGrowth
