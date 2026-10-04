module

public import ExactOverlaps.Entropy.StatisticFactors

/-!
# Entropy of determined statistics and complementary binary labels

A statistic recoverable from the conditioning observation has zero
conditional entropy. Replacing a binary label by its complement preserves
its conditional entropy exactly.
-/

@[expose] public section

namespace ExactOverlaps.Entropy

lemma averageStatisticConditionalEntropy_zero_of_factor {α β γ : Type*}
    (p : PMF α) (hp : p.support.Finite) (s : α → β) (g : α → γ) (k : β → γ)
    (hk : ∀ a ∈ p.support, g a = k (s a)) :
    averageStatisticConditionalEntropy p hp s g = 0 := by
  have he := finiteEntropy_map_eq_of_mutual_factors p hp
    (fun a ↦ (s a, g a)) s Prod.fst (fun b ↦ (b, k b))
    (fun _ _ ↦ rfl) (fun a ha ↦ Prod.ext rfl (hk a ha))
  rw [statisticEntropy_chain_rule p hp s g] at he
  linarith

lemma averageStatisticConditionalEntropy_bool_not {α β : Type*}
    (p : PMF α) (hp : p.support.Finite) (s : α → β) (g : α → Bool) :
    averageStatisticConditionalEntropy p hp s (fun a ↦ !g a) =
      averageStatisticConditionalEntropy p hp s g := by
  exact averageStatisticConditionalEntropy_eq_of_mutual_factors p hp s
    (fun a ↦ !g a) g Bool.not Bool.not (fun a _ ↦ by simp) (fun _ _ ↦ rfl)

end ExactOverlaps.Entropy
