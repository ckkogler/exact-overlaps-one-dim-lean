/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.DiscreteWJensen

/-! Pushing forward a genuine conditional law commutes with observing a statistic of its image. -/

@[expose] public section

open scoped Classical ENNReal

namespace ExactOverlaps.Entropy

variable {α β γ : Type*}

def mappedSupportAtom (p : PMF α) (F : α → β) (a : p.support) : (p.map F).support :=
  ⟨F a, (PMF.mem_support_map_iff F p _).mpr ⟨a, a.property, rfl⟩⟩

theorem conditionalAt_map (p : PMF α) (F : α → β) (f : β → γ) (a : p.support) :
    (conditionalAt p (fun x ↦ f (F x)) a).map F =
      conditionalAt (p.map F) f (mappedSupportAtom p F a) := by
  ext b
  rw [PMF.map_apply]
  simp only [conditionalAt, conditionalPMF_apply, mappedSupportAtom, PMF.map_comp]
  by_cases hb : f b = f (F a)
  · simp only [hb, ite_true]
    rw [show (p.map F) b = ∑' x, if b = F x then p x else 0 from PMF.map_apply F p b,
      div_eq_mul_inv, ← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro x
    by_cases hx : b = F x
    · simp only [← hx, hb, ite_true, div_eq_mul_inv, Function.comp_def]
    · simp [hx]
  · simp only [hb, ite_false]
    rw [ENNReal.tsum_eq_zero]
    intro x
    by_cases hx : b = F x
    · simp only [← hx, hb, ite_false, ite_true]
    · simp [hx]

end ExactOverlaps.Entropy

namespace ExactOverlaps.ConvolutionDisintegration

open Entropy FiniteProbability

variable {α β γ : Type*}

theorem meanConditionalMapW_map (p : PMF α) (hp : p.support.Finite)
    (F : α → β) (f : β → γ) (B : β → ℝ) (r : ℝ) :
    meanConditionalMapW (p.map F) (by simpa using hp.image F) f B r =
      meanConditionalMapW p hp (fun x ↦ f (F x)) (fun x ↦ B (F x)) r := by
  unfold meanConditionalMapW meanFiberFunctional
  rw [expectation_map p hp F]
  unfold expectation
  apply Finset.sum_congr rfl
  intro a ha
  have ha' : a ∈ p.support := by simpa using ha
  congr 1
  dsimp only
  have hleft := fiberFunctional_at (p.map F) (by simpa using hp.image F) f
    (fun q _ ↦ W (pmfLaw (q.map B)) r) (mappedSupportAtom p F ⟨a, ha'⟩)
  have hright := fiberFunctional_at p hp (fun x ↦ f (F x))
    (fun q _ ↦ W (pmfLaw (q.map (fun x ↦ B (F x)))) r) ⟨a, ha'⟩
  dsimp only [mappedSupportAtom] at hleft
  rw [hleft, hright]
  have hcond := conditionalAt_map p F f ⟨a, ha'⟩
  dsimp only [mappedSupportAtom] at hcond
  rw [← hcond, PMF.map_comp]
  rfl

theorem meanConditionalMapW_nonneg (p : PMF α) (hp : p.support.Finite)
    (f : α → β) (B : α → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ meanConditionalMapW p hp f B r := by
  rw [meanConditionalMapW, meanFiberFunctional_eq_sum]
  exact Finset.sum_nonneg (fun _ _ ↦ mul_nonneg ENNReal.toReal_nonneg (W_nonneg hr _))

theorem meanConditionalMapW_le_one (p : PMF α) (hp : p.support.Finite)
    (f : α → β) (B : α → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    meanConditionalMapW p hp f B r ≤ 1 := by
  let hf : (p.map f).support.Finite := by simpa using hp.image f
  let : Fintype (p.map f).support := hf.fintype
  rw [meanConditionalMapW, meanFiberFunctional_eq_sum]
  calc
    _ ≤ ∑ b : (p.map f).support, ((p.map f) b).toReal :=
      Finset.sum_le_sum (fun b _ ↦ mul_le_of_le_one_right ENNReal.toReal_nonneg (W_le_one hr _))
    _ = 1 := by
      rw [← sum_support_toReal (p.map f) hf]
      exact (Finset.sum_subtype hf.toFinset
        (by simp : ∀ b, b ∈ hf.toFinset ↔ b ∈ (p.map f).support)
        (fun b ↦ ((p.map f) b).toReal)).symm

end ExactOverlaps.ConvolutionDisintegration
