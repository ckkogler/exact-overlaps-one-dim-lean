module

public import ExactOverlaps.Entropy.Submodularity

/-!
# Entropy comparison for recoverable finite statistics

Deterministic recovery is required only on the positive-mass support. Two
statistics that recover one another have equal entropy, including their
mean conditional entropy given a further common observation.
-/

@[expose] public section

namespace ExactOverlaps.Entropy

lemma finiteEntropy_map_le_of_factor {α β γ : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (g : α → γ) (k : β → γ)
    (hk : ∀ a ∈ p.support, g a = k (f a)) :
    finiteEntropy (p.map g) (by simpa using hp.image g) ≤
      finiteEntropy (p.map f) (by simpa using hp.image f) := by
  have he : (p.map f).map k = p.map g := by
    rw [PMF.map_comp]
    exact map_congr_on_support p (fun a ha ↦ (hk a ha).symm)
  exact (finiteEntropy_congr he _ _).symm.trans_le
    (finiteEntropy_map_le (p.map f) (by simpa using hp.image f) k)

lemma finiteEntropy_map_eq_of_mutual_factors {α β γ : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (g : α → γ) (k : β → γ) (l : γ → β)
    (hk : ∀ a ∈ p.support, g a = k (f a))
    (hl : ∀ a ∈ p.support, f a = l (g a)) :
    finiteEntropy (p.map f) (by simpa using hp.image f) =
      finiteEntropy (p.map g) (by simpa using hp.image g) := by
  exact le_antisymm (finiteEntropy_map_le_of_factor p hp g f l hl)
    (finiteEntropy_map_le_of_factor p hp f g k hk)

lemma averageStatisticConditionalEntropy_eq_of_mutual_factors {α β γ δ : Type*}
    (p : PMF α) (hp : p.support.Finite) (s : α → δ) (f : α → β) (g : α → γ)
    (k : β → γ) (l : γ → β)
    (hk : ∀ a ∈ p.support, g a = k (f a))
    (hl : ∀ a ∈ p.support, f a = l (g a)) :
    averageStatisticConditionalEntropy p hp s f =
      averageStatisticConditionalEntropy p hp s g := by
  have he := finiteEntropy_map_eq_of_mutual_factors p hp
    (fun a ↦ (s a, f a)) (fun a ↦ (s a, g a))
    (fun z ↦ (z.1, k z.2)) (fun z ↦ (z.1, l z.2))
    (fun a ha ↦ Prod.ext rfl (hk a ha)) (fun a ha ↦ Prod.ext rfl (hl a ha))
  rw [statisticEntropy_chain_rule p hp s f, statisticEntropy_chain_rule p hp s g] at he
  exact add_left_cancel he

end ExactOverlaps.Entropy
