/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.RecordConditioning
public import ExactOverlaps.Probability.RectangularConditioning

/-! Exact rectangular conditioning when the second kernel depends only on the first observed label. -/

@[expose] public section

open scoped ENNReal Classical

namespace ExactOverlaps.StoppedConcatenation

open Entropy

variable {α β γ δ : Type*}

theorem jointMixture_map_labels (p : PMF α) (f : α → β) (k : β → PMF γ) (g : γ → δ) :
    (jointMixture p (fun a ↦ k (f a))).map (fun z ↦ (f z.1, g z.2)) =
      jointMixture (p.map f) (fun b ↦ (k b).map g) := by
  rw [← jointMixture_map_recordLabel p f (fun b ↦ (k b).map g),
    ← jointMixture_map_right p (fun a ↦ k (f a)) g, PMF.map_comp]
  rfl

def dependentMarginalLabel (p : PMF α) (f : α → β) (k : β → PMF γ) (g : γ → δ)
    (a : (p.map f).support) (b : ((k a).map g).support) :
    ((jointMixture p (fun x ↦ k (f x))).map (fun z ↦ (f z.1, g z.2))).support :=
  ⟨(a.val, b.val), by
    rw [PMF.mem_support_iff, jointMixture_map_labels, jointMixture_apply]
    exact mul_ne_zero a.property b.property⟩

theorem conditionalPMF_dependent_joint (p : PMF α) (f : α → β) (k : β → PMF γ)
    (g : γ → δ) (a : (p.map f).support) (b : ((k a).map g).support) :
    conditionalPMF (jointMixture p (fun x ↦ k (f x))) (fun z ↦ (f z.1, g z.2))
      (dependentMarginalLabel p f k g a b) =
        independentPair (conditionalPMF p f a) (conditionalPMF (k a) g b) := by
  ext z
  rcases z with ⟨x, y⟩
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  have hmass : ((jointMixture p (fun x ↦ k (f x))).map
      (fun z ↦ (f z.1, g z.2))) (a.val, b.val) = (p.map f) a * ((k a).map g) b := by
    rw [jointMixture_map_labels, jointMixture_apply]
  have ha := (marginal_toReal_pos p f a).ne'
  have hb := (marginal_toReal_pos (k a) g b).ne'
  by_cases hx : f x = a.val <;> by_cases hy : g y = b.val
  · simp [conditionalPMF_toReal, independentPair_apply, jointMixture_apply, ENNReal.toReal_mul,
      dependentMarginalLabel, hx, hy, hmass]
    field_simp [ha, hb]
  · simp [conditionalPMF_toReal, independentPair_apply, ENNReal.toReal_mul,
      dependentMarginalLabel, hx, hy]
  · simp [conditionalPMF_toReal, independentPair_apply, ENNReal.toReal_mul,
      dependentMarginalLabel, hx, hy]
  · simp [conditionalPMF_toReal, independentPair_apply, ENNReal.toReal_mul,
      dependentMarginalLabel, hx, hy]

end ExactOverlaps.StoppedConcatenation
