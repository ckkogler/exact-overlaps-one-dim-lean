/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.DiscreteWJensen
public import ExactOverlaps.ConvolutionDisintegration.ScalePower
public import Mathlib.Analysis.Convex.Jensen

/-! Scale comparison and concave-power Jensen for actual conditional W averages. -/

@[expose] public section

open scoped ENNReal Classical BigOperators

namespace ExactOverlaps.ConditionalW

open Entropy FiniteProbability ConvolutionDisintegration

theorem meanConditionalMapW_le_rpow_of_scale_window {α β : Type*}
    (p : PMF α) (hp : p.support.Finite) (f : α → β) (B : α → ℝ)
    {s t a : ℝ} (hs : 0 < s) (hst : s ≤ t) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (ha : a ≤ s ^ 2 / t ^ 2) :
    meanConditionalMapW p hp f B t ≤ (meanConditionalMapW p hp f B s) ^ a := by
  let hf : (p.map f).support.Finite := by simpa using hp.image f
  let : Fintype (p.map f).support := hf.fintype
  let v (b : (p.map f).support) := W (pmfLaw ((conditionalPMF p f b).map B)) s
  have hv (b : (p.map f).support) : 0 ≤ v b := W_nonneg hs.le _
  have hmass : ∑ b : (p.map f).support, ((p.map f) b).toReal = 1 := by
    simpa only [supportLaw_apply] using sum_pmf_toReal (supportLaw (p.map f))
  have hpoint (b : (p.map f).support) :
      W (pmfLaw ((conditionalPMF p f b).map B)) t ≤ (v b) ^ a :=
    (W_scale_power_le hs hst _).trans
      (Real.rpow_le_rpow_of_exponent_ge' (hv b) (W_le_one hs.le _) ha0 ha)
  rw [meanConditionalMapW, meanFiberFunctional_eq_sum,
    meanConditionalMapW, meanFiberFunctional_eq_sum]
  calc
    _ ≤ ∑ b : (p.map f).support, ((p.map f) b).toReal * (v b) ^ a :=
      Finset.sum_le_sum (fun b _ ↦ mul_le_mul_of_nonneg_left (hpoint b) ENNReal.toReal_nonneg)
    _ ≤ (∑ b : (p.map f).support, ((p.map f) b).toReal * v b) ^ a := by
      simpa only [smul_eq_mul] using (Real.concaveOn_rpow ha0 ha1).le_map_sum
        (t := Finset.univ) (w := fun b : (p.map f).support ↦ ((p.map f) b).toReal)
        (p := v) (fun _ _ ↦ ENNReal.toReal_nonneg) hmass (fun b _ ↦ hv b)

end ExactOverlaps.ConditionalW
