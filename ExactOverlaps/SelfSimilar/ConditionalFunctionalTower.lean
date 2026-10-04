module

public import ExactOverlaps.Probability.FiberAverages
public import ExactOverlaps.Probability.ConditionalVarianceTower

/-! A tower and refinement principle for functionals of genuine finite conditional laws. -/

@[expose] public section

open scoped BigOperators Classical

namespace ExactOverlaps.FiniteProbability

open Entropy

theorem fiberFunctional_conditional_at {α β γ : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (g : α → γ)
    (F : (q : PMF α) → q.support.Finite → ℝ) (b : (p.map f).support)
    (a : α) (ha : a ∈ (conditionalPMF p f b).support) :
    fiberFunctional (conditionalPMF p f b) (conditionalPMF_support_finite p hp f b) g F (g a) =
      fiberFunctional p hp (fun x ↦ (f x, g x)) F (f a, g a) := by
  have ha' := ha
  rw [conditionalPMF_support] at ha'
  have hc : g a ∈ ((conditionalPMF p f b).map g).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨a, ha, rfl⟩
  let c : ((conditionalPMF p f b).map g).support := ⟨g a, hc⟩
  have hd := joint_mem_support_of_conditional p f g b c
  rw [ha'.1]
  rw [fiberFunctional_positive _ _ g F c,
    fiberFunctional_positive p hp (fun x ↦ (f x, g x)) F ⟨(b.val, g a), hd⟩]
  exact finiteFunctional_congr F (conditionalPMF_conditionalPMF p f g b c) _ _

theorem meanFiberFunctional_tower {α β γ : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (g : α → γ)
    (F : (q : PMF α) → q.support.Finite → ℝ) :
    meanFiberFunctional p hp f (fun q hq ↦ meanFiberFunctional q hq g F) =
      meanFiberFunctional p hp (fun a ↦ (f a, g a)) F := by
  let : Fintype (p.map f).support := (show (p.map f).support.Finite from by
    simpa using hp.image f).fintype
  let v : α → ℝ := fun a ↦ fiberFunctional p hp (fun x ↦ (f x, g x)) F (f a, g a)
  rw [meanFiberFunctional_eq_sum]
  change (∑ b : (p.map f).support, _) = expectation p hp v
  rw [← sum_marginal_mul_expectation_conditional p hp f v]
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  unfold meanFiberFunctional expectation
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  exact fiberFunctional_conditional_at p hp f g F b a (by simpa using ha)

theorem meanFiberFunctional_congr_fibers {α β γ : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (g : α → γ)
    (F : (q : PMF α) → q.support.Finite → ℝ)
    (hfg : ∀ a b, f a = f b ↔ g a = g b) :
    meanFiberFunctional p hp f F = meanFiberFunctional p hp g F := by
  unfold meanFiberFunctional expectation
  apply Finset.sum_congr rfl
  intro a ha
  have ha' : a ∈ p.support := by simpa using ha
  congr 1
  dsimp only
  rw [fiberFunctional_at p hp f F ⟨a, ha'⟩, fiberFunctional_at p hp g F ⟨a, ha'⟩]
  exact finiteFunctional_congr F
    (conditionalAt_eq_of_fiber_eq p f g ⟨a, ha'⟩ (fun x ↦ hfg x a)) _ _

/-- A concave conditional-law functional decreases when the observation is refined. -/
theorem meanFiberFunctional_refinement_le {α β γ : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (k : β → γ)
    (F : (q : PMF α) → q.support.Finite → ℝ)
    (hconcave : ∀ (q : PMF α) (hq : q.support.Finite), meanFiberFunctional q hq f F ≤ F q hq) :
    meanFiberFunctional p hp f F ≤ meanFiberFunctional p hp (fun a ↦ k (f a)) F := by
  have h := meanFiberFunctional_mono p hp (fun a ↦ k (f a))
    (fun q hq ↦ meanFiberFunctional q hq f F) F (fun b ↦ hconcave _ _)
  rw [meanFiberFunctional_tower] at h
  have he := meanFiberFunctional_congr_fibers p hp
    (fun a ↦ (k (f a), f a)) f F
    (fun a b ↦ ⟨fun h ↦ (Prod.mk.inj h).2, fun h ↦ Prod.ext (congrArg k h) h⟩)
  rwa [he] at h

end ExactOverlaps.FiniteProbability
