module

public import ExactOverlaps.Probability.IndependentExpectations

/-!
# Independent conditioning on a rectangular observation

Conditioning an independent pair on one statistic of each coordinate leaves
the actual conditional law equal to the independent pair of its coordinate
conditional laws. Only positive-mass observed labels are admitted.
-/

@[expose] public section

open scoped ENNReal Classical

namespace ExactOverlaps.FiniteProbability

noncomputable def pairMarginalLabel {α β γ δ : Type*} (p : PMF α) (q : PMF β)
    (f : α → γ) (g : β → δ) (a : (p.map f).support) (b : (q.map g).support) :
    ((Entropy.independentPair p q).map (fun z ↦ (f z.1, g z.2))).support :=
  ⟨(a.val, b.val), by
    rw [independentPair_map_pair, Entropy.independentPair_support]
    exact ⟨a.property, b.property⟩⟩

theorem conditionalPMF_independentPair {α β γ δ : Type*} (p : PMF α) (q : PMF β)
    (f : α → γ) (g : β → δ) (a : (p.map f).support) (b : (q.map g).support) :
    Entropy.conditionalPMF (Entropy.independentPair p q) (fun z ↦ (f z.1, g z.2))
      (pairMarginalLabel p q f g a b) =
        Entropy.independentPair (Entropy.conditionalPMF p f a) (Entropy.conditionalPMF q g b) := by
  ext z
  rcases z with ⟨x, y⟩
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  have hmass : ((Entropy.independentPair p q).map (fun z ↦ (f z.1, g z.2))) (a.val, b.val) =
      (p.map f) a * (q.map g) b := by
    rw [independentPair_map_pair, Entropy.independentPair_apply]
  have ha := (Entropy.marginal_toReal_pos p f a).ne'
  have hb := (Entropy.marginal_toReal_pos q g b).ne'
  by_cases hx : f x = a.val <;> by_cases hy : g y = b.val
  · simp [Entropy.conditionalPMF_toReal, Entropy.independentPair_apply, ENNReal.toReal_mul,
      pairMarginalLabel, hx, hy, hmass]
    field_simp [ha, hb]
  · simp [Entropy.conditionalPMF_toReal, Entropy.independentPair_apply, ENNReal.toReal_mul,
      pairMarginalLabel, hx, hy]
  · simp [Entropy.conditionalPMF_toReal, Entropy.independentPair_apply, ENNReal.toReal_mul,
      pairMarginalLabel, hx, hy]
  · simp [Entropy.conditionalPMF_toReal, Entropy.independentPair_apply, ENNReal.toReal_mul,
      pairMarginalLabel, hx, hy]

end ExactOverlaps.FiniteProbability
