/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.ConvolutionDisintegration.DiracRepresentation

/-!
# Convexity of W

Mixing two actual admissible disintegrations preserves their mixture and
averages their costs. Approximating both infima proves convexity, including
zero coefficients; no minimizing disintegration is assumed to exist.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ExactOverlaps.ConvolutionDisintegration

def convexMix {α : Type*} [MeasurableSpace α] (a b : ℝ≥0) (hab : a + b = 1)
    (μ ν : ProbabilityMeasure α) : ProbabilityMeasure α :=
  ⟨(a : ℝ≥0∞) • (μ : Measure α) + (b : ℝ≥0∞) • (ν : Measure α),
    ⟨by simp [← ENNReal.coe_add, hab]⟩⟩

lemma mixture_convexMix (a b : ℝ≥0) (hab : a + b = 1)
    (θ φ : ProbabilityMeasure FactorFamily) :
    mixture (convexMix a b hab θ φ) = convexMix a b hab (mixture θ) (mixture φ) := by
  apply Subtype.ext
  change convolutionKernel ∘ₘ ((a : ℝ≥0∞) • (θ : Measure FactorFamily) +
    (b : ℝ≥0∞) • (φ : Measure FactorFamily)) = _
  rw [Measure.comp_add, Measure.comp_smul, Measure.comp_smul]
  rfl

lemma averageCost_convexMix (a b : ℝ≥0) (hab : a + b = 1)
    (θ φ : ProbabilityMeasure FactorFamily) (r : ℝ) :
    averageCost r (convexMix a b hab θ φ) =
      (a : ℝ) * averageCost r θ + (b : ℝ) * averageCost r φ := by
  change (∫ c, cost r c ∂((a : ℝ≥0∞) • (θ : Measure FactorFamily) +
    (b : ℝ≥0∞) • (φ : Measure FactorFamily))) = _
  rw [integral_add_measure ((integrable_cost r θ).smul_measure ENNReal.coe_ne_top)
    ((integrable_cost r φ).smul_measure ENNReal.coe_ne_top),
    integral_smul_measure, integral_smul_measure]
  rfl

lemma IsDisintegration.convexMix {μ ν : ProbabilityMeasure ℝ} {r : ℝ}
    {θ φ : ProbabilityMeasure FactorFamily} (hθ : IsDisintegration μ r θ)
    (hφ : IsDisintegration ν r φ) (a b : ℝ≥0) (hab : a + b = 1) :
    IsDisintegration (convexMix a b hab μ ν) r (convexMix a b hab θ φ) := by
  constructor
  · rw [mixture_convexMix, hθ.1, hφ.1]
  · change ∀ᵐ c ∂((a : ℝ≥0∞) • (θ : Measure FactorFamily) +
      (b : ℝ≥0∞) • (φ : Measure FactorFamily)), Admissible r c
    exact ae_add_measure_iff.mpr
      ⟨Measure.ae_smul_measure hθ.2 _, Measure.ae_smul_measure hφ.2 _⟩

lemma exists_cost_lt {r : ℝ} (hr : 0 ≤ r) (μ : ProbabilityMeasure ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ θ : ProbabilityMeasure FactorFamily,
      IsDisintegration μ r θ ∧ averageCost r θ < W μ r + ε := by
  obtain ⟨v, hv, hlt⟩ := exists_lt_of_csInf_lt (costValues_nonempty hr μ)
    (show sInf (costValues μ r) < W μ r + ε from lt_add_of_pos_right _ hε)
  obtain ⟨θ, hθ, rfl⟩ := hv
  exact ⟨θ, hθ, hlt⟩

theorem W_convexMix_le {r : ℝ} (hr : 0 ≤ r) (μ ν : ProbabilityMeasure ℝ)
    (a b : ℝ≥0) (hab : a + b = 1) :
    W (convexMix a b hab μ ν) r ≤ (a : ℝ) * W μ r + (b : ℝ) * W ν r := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨θ, hθ, hcθ⟩ := exists_cost_lt hr μ hε
  obtain ⟨φ, hφ, hcφ⟩ := exists_cost_lt hr ν hε
  have h := W_le_averageCost (hθ.convexMix hφ a b hab)
  rw [averageCost_convexMix] at h
  have ha := mul_le_mul_of_nonneg_left hcθ.le a.coe_nonneg
  have hb := mul_le_mul_of_nonneg_left hcφ.le b.coe_nonneg
  have habR : (a : ℝ) + (b : ℝ) = 1 := by exact_mod_cast hab
  calc
    _ ≤ (a : ℝ) * averageCost r θ + (b : ℝ) * averageCost r φ := h
    _ ≤ (a : ℝ) * (W μ r + ε) + (b : ℝ) * (W ν r + ε) := add_le_add ha hb
    _ = (a : ℝ) * W μ r + (b : ℝ) * W ν r + ε := by nlinarith [habR]

end ExactOverlaps.ConvolutionDisintegration
