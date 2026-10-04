module

public import ExactOverlaps.Entropy.ConditionalIncrement
public import ExactOverlaps.Entropy.StatisticFactors

/-!
# Conditional entropy averaged inside actual observation fibers

The finite chain rule identifies conditioning on two observations with
averaging a further conditional entropy inside the first observation's
actual normalized fibers. Null fibers are omitted by the support type.
-/

@[expose] public section

open scoped BigOperators Classical

namespace ExactOverlaps.Entropy

lemma averageStatisticConditionalEntropy_condition_eq_of_mutual_factors
    {α β γ δ : Type*} (p : PMF α) (hp : p.support.Finite)
    (f : α → β) (g : α → γ) (h : α → δ) (k : β → γ) (l : γ → β)
    (hk : ∀ a ∈ p.support, g a = k (f a))
    (hl : ∀ a ∈ p.support, f a = l (g a)) :
    averageStatisticConditionalEntropy p hp f h =
      averageStatisticConditionalEntropy p hp g h := by
  have he := finiteEntropy_map_eq_of_mutual_factors p hp f g k l hk hl
  have hj := finiteEntropy_map_eq_of_mutual_factors p hp
    (fun a ↦ (f a, h a)) (fun a ↦ (g a, h a))
    (fun z ↦ (k z.1, z.2)) (fun z ↦ (l z.1, z.2))
    (fun a ha ↦ Prod.ext (hk a ha) rfl) (fun a ha ↦ Prod.ext (hl a ha) rfl)
  rw [statisticEntropy_chain_rule p hp f h, statisticEntropy_chain_rule p hp g h, he] at hj
  exact add_left_cancel hj

lemma averageStatisticConditionalEntropy_condition_swap {α β γ δ : Type*}
    (p : PMF α) (hp : p.support.Finite) (f : α → β) (g : α → γ) (h : α → δ) :
    averageStatisticConditionalEntropy p hp (fun a ↦ (f a, g a)) h =
      averageStatisticConditionalEntropy p hp (fun a ↦ (g a, f a)) h := by
  exact averageStatisticConditionalEntropy_condition_eq_of_mutual_factors p hp
    (fun a ↦ (f a, g a)) (fun a ↦ (g a, f a)) h Prod.swap Prod.swap
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

theorem averageStatisticConditionalEntropy_tower {α β γ δ : Type*}
    (p : PMF α) (hp : p.support.Finite) (f : α → β) (g : α → γ) (h : α → δ) :
    (letI : Fintype (p.map f).support :=
      (show (p.map f).support.Finite from by simpa using hp.image f).fintype
    ∑ b : (p.map f).support, ((p.map f) b).toReal *
      averageStatisticConditionalEntropy (conditionalPMF p f b)
        (conditionalPMF_support_finite p hp f b) g h) =
      averageStatisticConditionalEntropy p hp (fun a ↦ (f a, g a)) h := by
  let : Fintype (p.map f).support :=
    (show (p.map f).support.Finite from by simpa using hp.image f).fintype
  have he : (∑ b : (p.map f).support, ((p.map f) b).toReal *
      averageStatisticConditionalEntropy (conditionalPMF p f b)
        (conditionalPMF_support_finite p hp f b) g h) =
      averageStatisticConditionalEntropy p hp f (fun a ↦ (g a, h a)) -
        averageStatisticConditionalEntropy p hp f g := by
    unfold averageStatisticConditionalEntropy
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b _
    have hc := statisticEntropy_chain_rule (conditionalPMF p f b)
      (conditionalPMF_support_finite p hp f b) g h
    unfold averageStatisticConditionalEntropy at hc
    rw [hc]
    ring
  rw [he, averageStatisticConditionalEntropy_increment]

end ExactOverlaps.Entropy
