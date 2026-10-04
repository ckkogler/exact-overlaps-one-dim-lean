/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.ConditionalW.DependentAverage

/-! Uniform bounds for record-dependent continuations and coarsening of the record. -/

@[expose] public section

open scoped Classical

namespace ExactOverlaps.ConditionalW

open Entropy FiniteProbability ConvolutionDisintegration

theorem fiberMapW_nonneg {α β : Type*} (p : PMF α) (hp : p.support.Finite)
    (f : α → β) (B : α → ℝ) {r : ℝ} (hr : 0 ≤ r) (b : β) :
    0 ≤ fiberFunctional p hp f (fun q _ ↦ W (pmfLaw (q.map B)) r) b := by
  unfold fiberFunctional
  split_ifs
  · exact W_nonneg hr _
  · exact le_rfl

theorem meanConditionalMapW_dependent_affine_uniform_cap {α β γ δ : Type*}
    [Countable α] [Countable γ]
    (p : PMF α) (hp : p.support.Finite) (f : α → β) (coef : β → ℝ)
    (k : β → PMF γ) (hk : ∀ a, (k a).support.Finite) (g : γ → δ)
    (B : α → ℝ) (C : γ → ℝ) {r cap : ℝ} (hr : 0 < r)
    (hf : ∀ x ∈ p.support, coef (f x) ≠ 0)
    (hcap : ∀ x ∈ p.support,
      meanConditionalMapW (k (f x)) (hk (f x)) g C (r / |coef (f x)|) ≤ cap) :
    meanConditionalMapW (jointMixture p (fun x ↦ k (f x)))
      (jointMixture_support_finite_of_finite p hp _ (fun x ↦ hk (f x)))
      (fun z ↦ (f z.1, g z.2)) (fun z ↦ B z.1 + coef (f z.1) * C z.2) r ≤
      cap * meanConditionalMapW p hp f B r := by
  calc
    _ ≤ expectation p hp (fun x ↦
        fiberFunctional p hp f (fun q _ ↦ W (pmfLaw (q.map B)) r) (f x) *
          meanConditionalMapW (k (f x)) (hk (f x)) g C (r / |coef (f x)|)) :=
      meanConditionalMapW_dependent_affine_le p hp f coef k hk g B C hr hf
    _ ≤ expectation p hp (fun x ↦ cap *
        fiberFunctional p hp f (fun q _ ↦ W (pmfLaw (q.map B)) r) (f x)) := by
      apply expectation_mono p hp
      intro x hx
      exact (mul_le_mul_of_nonneg_left (hcap x hx) (fiberMapW_nonneg p hp f B hr.le (f x))).trans_eq
        (mul_comm _ _)
    _ = cap * meanConditionalMapW p hp f B r :=
      expectation_const_mul p hp cap _

theorem meanConditionalMapW_dependent_affine_coarsened_cap {α β γ δ η : Type*}
    [Countable α] [Countable γ]
    (p : PMF α) (hp : p.support.Finite) (f : α → β) (coef : β → ℝ)
    (k : β → PMF γ) (hk : ∀ a, (k a).support.Finite) (g : γ → δ)
    (record : β × δ → η) (B : α → ℝ) (C : γ → ℝ) {r cap : ℝ} (hr : 0 < r)
    (hf : ∀ x ∈ p.support, coef (f x) ≠ 0)
    (hcap : ∀ x ∈ p.support,
      meanConditionalMapW (k (f x)) (hk (f x)) g C (r / |coef (f x)|) ≤ cap) :
    meanConditionalMapW (jointMixture p (fun x ↦ k (f x)))
      (jointMixture_support_finite_of_finite p hp _ (fun x ↦ hk (f x)))
      (fun z ↦ record (f z.1, g z.2)) (fun z ↦ B z.1 + coef (f z.1) * C z.2) r ≤
      cap * meanConditionalMapW p hp f B r := by
  have hcoarse := meanConditionalMapW_coarsening_le
    (jointMixture p (fun x ↦ k (f x)))
    (jointMixture_support_finite_of_finite p hp _ (fun x ↦ hk (f x)))
    (fun z : α × γ ↦ (f z.1, g z.2)) record
    (fun z : α × γ ↦ B z.1 + coef (f z.1) * C z.2) hr.le
  exact hcoarse.trans
    (meanConditionalMapW_dependent_affine_uniform_cap p hp f coef k hk g B C hr hf hcap)

end ExactOverlaps.ConditionalW
