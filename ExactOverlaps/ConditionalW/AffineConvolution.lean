/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.DiscreteWJensen
public import ExactOverlaps.Entropy.DiscreteMeasureConvolution
public import ExactOverlaps.ConvolutionDisintegration.ConvolutionBound
public import ExactOverlaps.ConvolutionDisintegration.Affine

/-! Actual affine sums of two independent discrete laws and their W bound. -/

@[expose] public section

open MeasureTheory

namespace ExactOverlaps.ConditionalW

open Entropy ConvolutionDisintegration

theorem map_eq_of_eq_on_support {α β : Type*} (p : PMF α) (f g : α → β)
    (h : ∀ a ∈ p.support, f a = g a) : p.map f = p.map g := by
  classical
  ext b
  rw [PMF.map_apply, PMF.map_apply]
  apply tsum_congr
  intro a
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · have hz : p a = 0 := by simpa using ha
    simp [hz]

theorem independent_affine_sum_law {α β : Type*} [Countable α] [Countable β]
    (p : PMF α) (q : PMF β) (B : α → ℝ) (C : β → ℝ) (a : ℝ) :
    pmfLaw ((independentPair p q).map (fun z ↦ B z.1 + a * C z.2)) =
      realConvolution (pmfLaw (p.map B)) ((pmfLaw (q.map C)).map (fun x ↦ a * x)) := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  have hB : Measurable B := measurable_of_countable _
  have hC : Measurable C := measurable_of_countable _
  have hscale : Measurable (fun x : ℝ ↦ a * x) := by fun_prop
  have hsum : Measurable (fun z : α × β ↦ B z.1 + a * C z.2) := by fun_prop
  apply ProbabilityMeasure.toMeasure_injective
  change (((independentPair p q).map (fun z ↦ B z.1 + a * C z.2)).toMeasure) =
    (((p.map B).toMeasure).prod (((q.map C).toMeasure).map (fun x ↦ a * x))).map
      (fun z : ℝ × ℝ ↦ z.1 + z.2)
  rw [← PMF.toMeasure_map _ _ hsum, independentPair_toMeasure,
    ← PMF.toMeasure_map _ _ hB, ← PMF.toMeasure_map _ _ hC,
    Measure.map_map hscale hC, Measure.map_prod_map _ _ hB (hscale.comp hC),
    Measure.map_map measurable_add (hB.prodMap (hscale.comp hC))]
  rfl

theorem W_independent_affine_sum_le {α β : Type*} [Countable α] [Countable β]
    (p : PMF α) (q : PMF β) (B : α → ℝ) (C : β → ℝ)
    {a r : ℝ} (ha : a ≠ 0) (hr : 0 < r) :
    W (pmfLaw ((independentPair p q).map (fun z ↦ B z.1 + a * C z.2))) r ≤
      W (pmfLaw (p.map B)) r * W (pmfLaw (q.map C)) (r / |a|) := by
  rw [independent_affine_sum_law]
  have h := W_convolution_le hr.le (pmfLaw (p.map B))
    ((pmfLaw (q.map C)).map (fun x ↦ a * x))
  have he := W_map_affine ha hr (pmfLaw (q.map C)) 0
  simp only [add_zero] at he
  rwa [he] at h

end ExactOverlaps.ConditionalW
