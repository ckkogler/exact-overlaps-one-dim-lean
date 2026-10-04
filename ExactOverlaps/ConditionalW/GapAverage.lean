/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.ConditionalW.AffineAverage
public import ExactOverlaps.ConditionalW.ScaleAverage
public import ExactOverlaps.StoppedConcatenation.GapConditioning

/-! Averaging the actual posterior after retaining an independent gap word. -/

@[expose] public section

open scoped Classical

namespace ExactOverlaps.ConditionalW

open Entropy FiniteProbability ConvolutionDisintegration StoppedConcatenation

theorem meanConditionalMapW_gap_affine {α β γ : Type*}
    (p : PMF α) (hp : p.support.Finite) (q : PMF β) (hq : q.support.Finite)
    (f : β → γ) (A D : α → ℝ) (B : β → ℝ) {r : ℝ} (hr : 0 < r)
    (hA : ∀ x ∈ p.support, A x ≠ 0) :
    meanConditionalMapW (independentPair p q) (independentPair_support_finite p q hp hq)
      (fun z ↦ (z.1, f z.2)) (fun z ↦ D z.1 + A z.1 * B z.2) r =
      expectation p hp (fun x ↦ meanConditionalMapW q hq f B (r / |A x|)) := by
  unfold meanConditionalMapW meanFiberFunctional
  rw [expectation_independentPair p q hp hq]
  unfold expectation
  apply Finset.sum_congr rfl
  intro a ha
  have ha' : a ∈ p.support := by simpa using ha
  congr 1
  apply Finset.sum_congr rfl
  intro b hb
  have hb' : b ∈ q.support := by simpa using hb
  congr 1
  let c : (q.map f).support :=
    ⟨f b, (PMF.mem_support_map_iff f q _).mpr ⟨b, hb', rfl⟩⟩
  dsimp only
  have hl := fiberFunctional_positive (independentPair p q)
    (independentPair_support_finite p q hp hq) (fun z ↦ (z.1, f z.2))
    (fun u _ ↦ W (pmfLaw (u.map (fun z ↦ D z.1 + A z.1 * B z.2))) r)
    (gapMarginalLabel p q f ⟨a, ha'⟩ c)
  have hright := fiberFunctional_positive q hq f
    (fun u _ ↦ W (pmfLaw (u.map B)) (r / |A a|)) c
  change fiberFunctional _ _ _ _ (a, f b) = _ at hl
  change fiberFunctional _ _ _ _ (f b) = _ at hright
  rw [hl, hright, conditionalPMF_gap_map]
  have he : (fun x : β ↦ D a + A a * B x) = (fun x ↦ A a * B x + D a) := by
    funext x
    exact add_comm _ _
  dsimp only
  rw [he, pmfLaw_map_affine, W_map_affine (hA a ha') hr]

theorem meanConditionalMapW_gap_affine_le_rpow {α β γ : Type*}
    (p : PMF α) (hp : p.support.Finite) (q : PMF β) (hq : q.support.Finite)
    (f : β → γ) (A D : α → ℝ) (B : β → ℝ) {r s a : ℝ}
    (hr : 0 < r) (hs : 0 < s) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hA : ∀ x ∈ p.support, A x ≠ 0)
    (hwindow : ∀ x ∈ p.support, s ≤ r / |A x| ∧ a ≤ s ^ 2 / (r / |A x|) ^ 2) :
    meanConditionalMapW (independentPair p q) (independentPair_support_finite p q hp hq)
      (fun z ↦ (z.1, f z.2)) (fun z ↦ D z.1 + A z.1 * B z.2) r ≤
      (meanConditionalMapW q hq f B s) ^ a := by
  rw [meanConditionalMapW_gap_affine p hp q hq f A D B hr hA]
  calc
    _ ≤ expectation p hp (fun _ ↦ (meanConditionalMapW q hq f B s) ^ a) := by
      apply expectation_mono p hp
      intro x hx
      exact meanConditionalMapW_le_rpow_of_scale_window q hq f B hs
        (hwindow x hx).1 ha0 ha1 (hwindow x hx).2
    _ = _ := expectation_const p hp _

end ExactOverlaps.ConditionalW
