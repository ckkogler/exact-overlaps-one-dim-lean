module

public import ExactOverlaps.Probability.OrderedFinitePresentation

/-!
# A common increasing grid for finitely many finite real laws

The union of the marginal supports, together with zero, is a finite nonempty
ordered grid. Every marginal is reindexed on the same grid by an exact PMF
push-forward. Points unused by a marginal simply have zero mass; the extra
point also makes the empty-family case well-defined.
-/

@[expose] public section

open scoped Classical

namespace ExactOverlaps.Poisson

structure CommonOrderedPresentation {ι : Type*} (p : ι → PMF ℝ) where
  size : ℕ
  law : ι → PMF (Fin (size + 1))
  coordinate : ℕ → ℝ
  strictlyOrdered : StrictMono (fun z : Fin (size + 1) ↦ coordinate z.val)
  map_eq : ∀ i, (law i).map (fun z ↦ coordinate z.val) = p i

lemma exists_commonOrderedPresentation {ι : Type*} [Fintype ι] (p : ι → PMF ℝ)
    (hp : ∀ i, (p i).support.Finite) : Nonempty (CommonOrderedPresentation p) := by
  let s : Set ℝ := insert 0 (⋃ i, (p i).support)
  have hs : s.Finite := (Set.finite_iUnion hp).insert 0
  let : Fintype s := hs.fintype
  let : Nonempty s := ⟨⟨0, Set.mem_insert _ _⟩⟩
  let n := Fintype.card s - 1
  have hn : Fintype.card s = n + 1 := by
    have hpos := Fintype.card_pos (α := s)
    dsimp [n]
    omega
  let e : Fin (n + 1) ≃o s := Fintype.orderIsoFinOfCardEq s hn
  let emb (i : ι) (a : (p i).support) : s :=
    ⟨a.val, Set.mem_insert_of_mem 0 (Set.mem_iUnion.mpr ⟨i, a.property⟩)⟩
  let q (i : ι) : PMF (Fin (n + 1)) := (Entropy.supportLaw (p i)).map (fun a ↦ e.symm (emb i a))
  let x : ℕ → ℝ := fun k ↦ if hk : k < n + 1 then (e ⟨k, hk⟩).val else 0
  have hx (a : Fin (n + 1)) : x a.val = (e a).val := by
    dsimp only [x]
    rw [dite_eq_left a.isLt]
  refine ⟨⟨n, q, x, ?_, ?_⟩⟩
  · intro a b hab
    simp only [hx]
    exact e.strictMono hab
  · intro i
    change ((Entropy.supportLaw (p i)).map (fun a ↦ e.symm (emb i a))).map (fun a ↦ x a.val) = p i
    rw [PMF.map_comp]
    have he : (fun a : Fin (n + 1) ↦ x a.val) ∘ (fun a ↦ e.symm (emb i a)) = Subtype.val := by
      funext a
      change x (e.symm (emb i a)).val = a.val
      rw [hx]
      simp [emb]
    rw [he, Entropy.supportLaw_map_val]

noncomputable def commonOrderedPresentation {ι : Type*} [Fintype ι] (p : ι → PMF ℝ)
    (hp : ∀ i, (p i).support.Finite) : CommonOrderedPresentation p :=
  (exists_commonOrderedPresentation p hp).some

end ExactOverlaps.Poisson
