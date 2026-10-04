module

public import ExactOverlaps.Entropy.ConditionalConcavity
public import Mathlib.Data.Fintype.Sort

/-!
# Ordered finite presentations of real probability laws

A finite real law can be reindexed by its increasingly ordered support.
The indexed probability law maps back exactly to the original law; values
outside the finite index range play no role.
-/

@[expose] public section

open scoped Classical

namespace ExactOverlaps.Poisson

structure OrderedFinitePresentation (p : PMF ℝ) where
  size : ℕ
  law : PMF (Fin (size + 1))
  coordinate : ℕ → ℝ
  strictlyOrdered : StrictMono (fun z : Fin (size + 1) ↦ coordinate z.val)
  map_eq : law.map (fun z ↦ coordinate z.val) = p

lemma exists_orderedFinitePresentation (p : PMF ℝ) (hp : p.support.Finite) :
    Nonempty (OrderedFinitePresentation p) := by
  let : Fintype p.support := hp.fintype
  let : Nonempty p.support := p.support_nonempty.to_subtype
  let n := Fintype.card p.support - 1
  have hn : Fintype.card p.support = n + 1 := by
    have hpos := Fintype.card_pos (α := p.support)
    dsimp [n]
    omega
  let e : Fin (n + 1) ≃o p.support := Fintype.orderIsoFinOfCardEq p.support hn
  let q : PMF (Fin (n + 1)) := (Entropy.supportLaw p).map e.symm
  let x : ℕ → ℝ := fun k ↦ if hk : k < n + 1 then (e ⟨k, hk⟩).val else 0
  have hx (i : Fin (n + 1)) : x i.val = (e i).val := by
    dsimp only [x]
    rw [dite_eq_left i.isLt]
  refine ⟨⟨n, q, x, ?_, ?_⟩⟩
  · intro i j hij
    simp only [hx]
    exact e.strictMono hij
  · change ((Entropy.supportLaw p).map e.symm).map (fun i ↦ x i.val) = p
    rw [PMF.map_comp]
    have he : (fun i : Fin (n + 1) ↦ x i.val) ∘ e.symm = Subtype.val := by
      funext s
      change x (e.symm s).val = s.val
      rw [hx]
      simp
    rw [he, Entropy.supportLaw_map_val]

/-- A chosen increasing support presentation of a finite real law. -/
noncomputable def orderedFinitePresentation (p : PMF ℝ) (hp : p.support.Finite) :
    OrderedFinitePresentation p := (exists_orderedFinitePresentation p hp).some

end ExactOverlaps.Poisson
