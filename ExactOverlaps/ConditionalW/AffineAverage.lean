/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.DiscreteWJensen
public import ExactOverlaps.ConvolutionDisintegration.Affine

/-! Signed affine changes and injective recoding of genuine conditional W averages. -/

@[expose] public section

open MeasureTheory

namespace ExactOverlaps.ConditionalW

open Entropy FiniteProbability ConvolutionDisintegration

theorem pmfLaw_map_affine {α : Type*} (p : PMF α) (B : α → ℝ) (a b : ℝ) :
    pmfLaw (p.map (fun x ↦ a * B x + b)) =
      (pmfLaw (p.map B)).map (fun x ↦ a * x + b) := by
  have he : p.map (fun x ↦ a * B x + b) =
      (p.map B).map (fun x ↦ a * x + b) := by rw [PMF.map_comp]; rfl
  rw [he]
  apply ProbabilityMeasure.toMeasure_injective
  exact (PMF.toMeasure_map (fun x : ℝ ↦ a * x + b) (p.map B) (by fun_prop)).symm

theorem meanConditionalMapW_affine {α β : Type*} (p : PMF α) (hp : p.support.Finite)
    (f : α → β) (B : α → ℝ) {a r : ℝ} (ha : a ≠ 0) (hr : 0 < r) (b : ℝ) :
    meanConditionalMapW p hp f (fun x ↦ a * B x + b) r =
      meanConditionalMapW p hp f B (r / |a|) := by
  rw [meanConditionalMapW, meanConditionalMapW, meanFiberFunctional_eq_sum,
    meanFiberFunctional_eq_sum]
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  rw [pmfLaw_map_affine, W_map_affine ha hr]

theorem meanConditionalMapW_observation_injective {α β γ : Type*}
    (p : PMF α) (hp : p.support.Finite) (f : α → β) (k : β → γ)
    (hk : Function.Injective k) (B : α → ℝ) (r : ℝ) :
    meanConditionalMapW p hp (fun x ↦ k (f x)) B r = meanConditionalMapW p hp f B r := by
  exact meanFiberFunctional_congr_fibers p hp _ f _ (fun x y ↦ hk.eq_iff)

theorem meanConditionalMapW_affine_composition {α : Type*}
    (p : PMF α) (hp : p.support.Finite) (R B : α → ℝ)
    {a r : ℝ} (ha : a ≠ 0) (hr : 0 < r) (b : ℝ) :
    meanConditionalMapW p hp (fun x ↦ a * R x) (fun x ↦ a * B x + b) r =
      meanConditionalMapW p hp R B (r / |a|) := by
  rw [meanConditionalMapW_observation_injective p hp R (fun x ↦ a * x)
    (fun _ _ h ↦ mul_left_cancel₀ ha h), meanConditionalMapW_affine p hp R B ha hr]

end ExactOverlaps.ConditionalW
