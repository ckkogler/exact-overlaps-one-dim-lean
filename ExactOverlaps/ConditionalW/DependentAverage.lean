/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.ConditionalW.DependentFiber
public import ExactOverlaps.ConditionalW.FiniteMixtureAverage

/-!
Averaged conditional W for an actual affine composition whose second law
depends only on the first signed ratio. The posterior product factorization
and the finite expectation identity are both proved for the genuine laws.
-/

@[expose] public section

open scoped Classical

namespace ExactOverlaps.ConditionalW

open Entropy FiniteProbability ConvolutionDisintegration StoppedConcatenation

theorem meanConditionalMapW_dependent_affine_le {α β γ δ : Type*}
    [Countable α] [Countable γ]
    (p : PMF α) (hp : p.support.Finite) (f : α → β) (coef : β → ℝ)
    (k : β → PMF γ) (hk : ∀ a, (k a).support.Finite) (g : γ → δ)
    (B : α → ℝ) (C : γ → ℝ) {r : ℝ} (hr : 0 < r)
    (hf : ∀ x ∈ p.support, coef (f x) ≠ 0) :
    meanConditionalMapW (jointMixture p (fun x ↦ k (f x)))
      (jointMixture_support_finite_of_finite p hp _ (fun x ↦ hk (f x)))
      (fun z ↦ (f z.1, g z.2)) (fun z ↦ B z.1 + coef (f z.1) * C z.2) r ≤
      expectation p hp (fun x ↦
        fiberFunctional p hp f (fun q _ ↦ W (pmfLaw (q.map B)) r) (f x) *
          meanConditionalMapW (k (f x)) (hk (f x)) g C (r / |coef (f x)|)) := by
  let J := jointMixture p (fun x ↦ k (f x))
  let hJ : J.support.Finite :=
    jointMixture_support_finite_of_finite p hp _ (fun x ↦ hk (f x))
  let F : α × γ → ℝ := fun z ↦ B z.1 + coef (f z.1) * C z.2
  let G : α × γ → ℝ := fun z ↦ fiberFunctional J hJ
    (fun z ↦ (f z.1, g z.2)) (fun q _ ↦ W (pmfLaw (q.map F)) r) (f z.1, g z.2)
  let A : β → ℝ := fiberFunctional p hp f (fun q _ ↦ W (pmfLaw (q.map B)) r)
  let V : β → δ → ℝ := fun a ↦ fiberFunctional (k a) (hk a) g
    (fun q _ ↦ W (pmfLaw (q.map C)) (r / |coef a|))
  have hpoint (z : α × γ) (hz : z ∈ J.support) : G z ≤ A (f z.1) * V (f z.1) (g z.2) := by
    have hne : p z.1 * k (f z.1) z.2 ≠ 0 := by
      have he := jointMixture_apply p (fun x ↦ k (f x)) z.1 z.2
      change J z ≠ 0 at hz
      change J z = p z.1 * k (f z.1) z.2 at he
      rwa [← he]
    have hx : z.1 ∈ p.support := left_ne_zero_of_mul hne
    have hy : z.2 ∈ (k (f z.1)).support := right_ne_zero_of_mul hne
    let a : (p.map f).support :=
      ⟨f z.1, (PMF.mem_support_map_iff f p _).mpr ⟨z.1, hx, rfl⟩⟩
    let b : ((k a).map g).support :=
      ⟨g z.2, (PMF.mem_support_map_iff g (k a) _).mpr ⟨z.2, hy, rfl⟩⟩
    have hG : G z = W (pmfLaw ((conditionalPMF J (fun z ↦ (f z.1, g z.2))
        (dependentMarginalLabel p f k g a b)).map F)) r :=
      fiberFunctional_positive J hJ _ _ (dependentMarginalLabel p f k g a b)
    have hA : A (f z.1) = W (pmfLaw ((conditionalPMF p f a).map B)) r :=
      fiberFunctional_positive p hp f _ a
    have hV : V (f z.1) (g z.2) =
        W (pmfLaw ((conditionalPMF (k a) g b).map C)) (r / |coef a.val|) :=
      fiberFunctional_positive (k a) (hk a) g _ b
    rw [hG, hA, hV]
    exact dependent_fiber_affine_W_le p f coef k g B C a b hr (hf z.1 hx)
  have hav := expectation_mono J hJ hpoint
  change expectation J hJ G ≤ expectation p hp
    (fun x ↦ A (f x) * meanConditionalMapW (k (f x)) (hk (f x)) g C (r / |coef (f x)|))
  calc
    expectation J hJ G ≤ expectation J hJ (fun z ↦ A (f z.1) * V (f z.1) (g z.2)) := hav
    _ = expectation p hp (fun x ↦ A (f x) *
        meanConditionalMapW (k (f x)) (hk (f x)) g C (r / |coef (f x)|)) := by
      rw [expectation_jointMixture p hp (fun x ↦ k (f x)) (fun x ↦ hk (f x))]
      simp only [expectation_const_mul]
      rfl

end ExactOverlaps.ConditionalW
