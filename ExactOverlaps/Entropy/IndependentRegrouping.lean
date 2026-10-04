module

public import ExactOverlaps.Probability.IndependentExpectations

/-!
# Regrouping actual independent product laws

Swapping or reassociating finite product coordinates preserves the expected
product law. The regrouping identity also applies when two independent
statistics are first extracted from one coordinate.
-/

@[expose] public section

namespace ExactOverlaps.Entropy

lemma independentPair_swap {α β : Type*} (p : PMF α) (q : PMF β) :
    (independentPair p q).map Prod.swap = independentPair q p := by
  ext z
  rcases z with ⟨b, a⟩
  change (independentPair p q).map Prod.swap (Prod.swap (a, b)) = _
  rw [map_apply_of_injective _ Prod.swap_injective]
  simp only [independentPair_apply, mul_comm]

lemma independentPair_swap_first_two {α β γ : Type*}
    (p : PMF α) (q : PMF β) (r : PMF γ) :
    (independentPair p (independentPair q r)).map (fun z ↦ (z.2.1, (z.1, z.2.2))) =
      independentPair q (independentPair p r) := by
  let f : α × (β × γ) → β × (α × γ) := fun z ↦ (z.2.1, (z.1, z.2.2))
  have hf : Function.Injective f := by
    intro a b h
    have h' : (a.2.1, (a.1, a.2.2)) = (b.2.1, (b.1, b.2.2)) := h
    apply Prod.ext
    · exact (Prod.mk.inj (Prod.mk.inj h').2).1
    · exact Prod.ext (Prod.mk.inj h').1 (Prod.mk.inj (Prod.mk.inj h').2).2
  ext z
  rcases z with ⟨b, a, c⟩
  change (independentPair p (independentPair q r)).map f (f (a, (b, c))) = _
  rw [map_apply_of_injective _ hf]
  simp only [independentPair_apply]
  ring

lemma independentPair_regroup {α β γ δ : Type*} (p : PMF α) (r : PMF β)
    (f : β → γ) (g : β → δ) (q : PMF γ) (v : PMF δ)
    (h : r.map (fun b ↦ (f b, g b)) = independentPair q v) :
    (independentPair p r).map (fun z ↦ (f z.2, (z.1, g z.2))) =
      independentPair q (independentPair p v) := by
  have he : (independentPair p r).map (fun z ↦ (f z.2, (z.1, g z.2))) =
      ((independentPair p r).map (fun z ↦ (z.1, (f z.2, g z.2)))).map
        (fun z ↦ (z.2.1, (z.1, z.2.2))) := by
    rw [PMF.map_comp]
    rfl
  rw [he, independentPair_map_right p r (fun b ↦ (f b, g b)), h,
    independentPair_swap_first_two]

end ExactOverlaps.Entropy
