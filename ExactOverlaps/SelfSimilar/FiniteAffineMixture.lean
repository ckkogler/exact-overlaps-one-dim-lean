module

public import ExactOverlaps.Entropy.ConvolutionMixture

/-!
Convolving a finite translation law with a dilated probability measure
is exactly the corresponding finite affine mixture. No sign restriction
is imposed on the dilation.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal Classical BigOperators

namespace ExactOverlaps.SelfSimilar

theorem finite_translation_measure {α : Type*} [Fintype α]
    (p : PMF α) (b : α → ℝ) :
    (p.map b).toMeasure = ∑ a, p a • Measure.dirac (b a) := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSingletonClass α := ⟨fun _ ↦ trivial⟩
  have hb : Measurable b := fun _ _ ↦ trivial
  apply Measure.ext
  intro E hE
  rw [← PMF.toMeasure_map b p hb, Measure.map_apply hb hE, PMF.toMeasure_apply_fintype]
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ hE]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : b a ∈ E <;> simp [ha]

theorem finite_translation_convolution {α : Type*} [Fintype α]
    (p : PMF α) (b : α → ℝ) (μ : ProbabilityMeasure ℝ) (t : ℝ) :
    (p.map b).toMeasure ∗ (μ : Measure ℝ).map (fun x ↦ t * x) =
      ∑ a, p a • (μ : Measure ℝ).map (fun x ↦ t * x + b a) := by
  rw [finite_translation_measure, Entropy.measure_finset_sum_conv]
  apply Finset.sum_congr rfl
  intro a _
  rw [Measure.conv_smul_left, Measure.dirac_conv,
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 2
  funext x
  simp only [Function.comp_apply]
  ring

end ExactOverlaps.SelfSimilar
