/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.DependentConditioning
public import ExactOverlaps.Probability.IndependentExpectations

/-! Retaining an entire independent gap leaves precisely the head-block conditional law. -/

@[expose] public section

open scoped Classical ENNReal

namespace ExactOverlaps.StoppedConcatenation

open Entropy FiniteProbability

variable {α β γ : Type*}

theorem conditionalPMF_id (p : PMF α) (a : p.support) :
    conditionalPMF p id ⟨a, by simpa only [PMF.map_id] using a.property⟩ = PMF.pure a.val := by
  ext x
  simp only [conditionalPMF_apply, PMF.map_id]
  by_cases h : x = a.val
  · subst x
    simp only [id_eq, ite_true, PMF.pure_apply_self]
    exact ENNReal.div_self a.property (p.apply_ne_top _)
  · simp [h, PMF.pure_apply]

noncomputable def gapMarginalLabel (p : PMF α) (q : PMF β) (f : β → γ)
    (a : p.support) (b : (q.map f).support) :
    ((independentPair p q).map (fun z ↦ (z.1, f z.2))).support :=
  pairMarginalLabel p q id f ⟨a, by simpa only [PMF.map_id] using a.property⟩ b

theorem conditionalPMF_gap (p : PMF α) (q : PMF β) (f : β → γ)
    (a : p.support) (b : (q.map f).support) :
    conditionalPMF (independentPair p q) (fun z ↦ (z.1, f z.2)) (gapMarginalLabel p q f a b) =
      independentPair (PMF.pure a.val) (conditionalPMF q f b) := by
  have h := conditionalPMF_independentPair p q id f
    ⟨a, by simpa only [PMF.map_id] using a.property⟩ b
  rw [conditionalPMF_id] at h
  exact h

theorem conditionalPMF_gap_map (p : PMF α) (q : PMF β) (f : β → γ)
    (a : p.support) (b : (q.map f).support) (B : α × β → ℝ) :
    (conditionalPMF (independentPair p q) (fun z ↦ (z.1, f z.2))
      (gapMarginalLabel p q f a b)).map B = (conditionalPMF q f b).map (fun x ↦ B (a, x)) := by
  rw [conditionalPMF_gap]
  simp only [independentPair, PMF.pure_bind, PMF.map_comp, Function.comp_def]

end ExactOverlaps.StoppedConcatenation
