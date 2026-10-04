module

public import ExactOverlaps.Entropy.Submodularity

/-!
# Conditional entropy gained by one additional statistic

The entropy chain rule identifies the exact gain from augmenting an
observation by another statistic, with the previous observation included
in the conditioning. All joint laws are push-forwards of the same law.
-/

@[expose] public section

namespace ExactOverlaps.Entropy

lemma finiteEntropy_pair_assoc {α β γ δ : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (g : α → γ) (h : α → δ) :
    finiteEntropy (p.map (fun a ↦ (f a, (g a, h a))))
        (by simpa using hp.image (fun a ↦ (f a, (g a, h a)))) =
      finiteEntropy (p.map (fun a ↦ ((f a, g a), h a)))
        (by simpa using hp.image (fun a ↦ ((f a, g a), h a))) := by
  have he := finiteEntropy_map_of_injective
    (p.map (fun a ↦ ((f a, g a), h a)))
    (show (p.map (fun a ↦ ((f a, g a), h a))).support.Finite from
      by simpa using hp.image (fun a ↦ ((f a, g a), h a)))
    (Equiv.prodAssoc β γ δ).injective
  simpa only [PMF.map_comp, Function.comp_def, Equiv.prodAssoc_apply] using he

theorem averageStatisticConditionalEntropy_chain_rule {α β γ δ : Type*}
    (p : PMF α) (hp : p.support.Finite) (f : α → β) (g : α → γ) (h : α → δ) :
    averageStatisticConditionalEntropy p hp f (fun a ↦ (g a, h a)) =
      averageStatisticConditionalEntropy p hp f g +
        averageStatisticConditionalEntropy p hp (fun a ↦ (f a, g a)) h := by
  have h₁ := statisticEntropy_chain_rule p hp f (fun a ↦ (g a, h a))
  have h₂ := statisticEntropy_chain_rule p hp (fun a ↦ (f a, g a)) h
  have h₃ := statisticEntropy_chain_rule p hp f g
  have he := finiteEntropy_pair_assoc p hp f g h
  linarith

theorem averageStatisticConditionalEntropy_increment {α β γ δ : Type*}
    (p : PMF α) (hp : p.support.Finite) (f : α → β) (g : α → γ) (h : α → δ) :
    averageStatisticConditionalEntropy p hp f (fun a ↦ (g a, h a)) -
        averageStatisticConditionalEntropy p hp f g =
      averageStatisticConditionalEntropy p hp (fun a ↦ (f a, g a)) h := by
  rw [averageStatisticConditionalEntropy_chain_rule]
  ring

lemma averageStatisticConditionalEntropy_pair_mono {α β γ δ : Type*}
    (p : PMF α) (hp : p.support.Finite) (f : α → β) (g : α → γ) (h : α → δ) :
    averageStatisticConditionalEntropy p hp f g ≤
      averageStatisticConditionalEntropy p hp f (fun a ↦ (g a, h a)) := by
  rw [averageStatisticConditionalEntropy_chain_rule]
  apply le_add_of_nonneg_right
  unfold averageStatisticConditionalEntropy
  exact Finset.sum_nonneg (fun _ _ ↦ mul_nonneg ENNReal.toReal_nonneg
    (finiteEntropy_nonneg _ _))

end ExactOverlaps.Entropy
