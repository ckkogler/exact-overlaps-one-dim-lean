module

public import ExactOverlaps.Entropy.Submodularity

/-!
# Conditional entropy through an actual PMF push-forward

Only the two observed statistics matter for their conditional entropy.
The joint-law chain rule proves exact transport through an arbitrary
deterministic map of the underlying finite probability space.
-/

@[expose] public section

namespace ExactOverlaps.Entropy

lemma averageStatisticConditionalEntropy_congr {α β γ : Type*} {p q : PMF α}
    (h : p = q) (hp : p.support.Finite) (hq : q.support.Finite) (f : α → β) (g : α → γ) :
    averageStatisticConditionalEntropy p hp f g = averageStatisticConditionalEntropy q hq f g := by
  cases h
  rfl

lemma averageStatisticConditionalEntropy_map {α β γ δ : Type*}
    (p : PMF α) (hp : p.support.Finite) (k : α → β) (f : β → γ) (g : β → δ) :
    averageStatisticConditionalEntropy (p.map k) (by simpa using hp.image k) f g =
      averageStatisticConditionalEntropy p hp (fun a ↦ f (k a)) (fun a ↦ g (k a)) := by
  have h₁ := statisticEntropy_chain_rule (p.map k) (by simpa using hp.image k) f g
  have h₂ := statisticEntropy_chain_rule p hp (fun a ↦ f (k a)) (fun a ↦ g (k a))
  simp only [PMF.map_comp, Function.comp_def] at h₁
  linarith

end ExactOverlaps.Entropy
