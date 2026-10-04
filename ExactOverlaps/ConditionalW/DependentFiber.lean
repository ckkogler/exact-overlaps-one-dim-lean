/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.ConditionalW.AffineConvolution
public import ExactOverlaps.StoppedConcatenation.DependentConditioning

/-! The affine convolution inequality on each actual positive conditional fiber. -/

@[expose] public section

namespace ExactOverlaps.ConditionalW

open Entropy ConvolutionDisintegration StoppedConcatenation

theorem dependent_fiber_affine_W_le {α β γ δ : Type*} [Countable α] [Countable γ]
    (p : PMF α) (f : α → β) (A : β → ℝ) (k : β → PMF γ) (g : γ → δ)
    (B : α → ℝ) (C : γ → ℝ)
    (a : (p.map f).support) (b : ((k a).map g).support)
    {r : ℝ} (hr : 0 < r) (ha : A a.val ≠ 0) :
    W (pmfLaw ((conditionalPMF (jointMixture p (fun x ↦ k (f x)))
        (fun z ↦ (f z.1, g z.2)) (dependentMarginalLabel p f k g a b)).map
          (fun z ↦ B z.1 + A (f z.1) * C z.2))) r ≤
      W (pmfLaw ((conditionalPMF p f a).map B)) r *
        W (pmfLaw ((conditionalPMF (k a) g b).map C)) (r / |A a.val|) := by
  rw [conditionalPMF_dependent_joint]
  have he : (independentPair (conditionalPMF p f a) (conditionalPMF (k a) g b)).map
      (fun z ↦ B z.1 + A (f z.1) * C z.2) =
      (independentPair (conditionalPMF p f a) (conditionalPMF (k a) g b)).map
        (fun z ↦ B z.1 + A a.val * C z.2) := by
    apply map_eq_of_eq_on_support
    intro z hz
    rw [independentPair_support] at hz
    have hx := hz.1
    rw [conditionalPMF_support] at hx
    rw [hx.1]
  rw [he]
  exact W_independent_affine_sum_le (conditionalPMF p f a)
    (conditionalPMF (k a) g b) B C ha hr

end ExactOverlaps.ConditionalW
