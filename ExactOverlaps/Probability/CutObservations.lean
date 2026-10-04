module

public import ExactOverlaps.Probability.PoissonRefinement
public import ExactOverlaps.Probability.ConditionalRefinement

/-!
# Observation cells of a finite cut state

The label of an atom records on which side of each active cut it lies. Two
atoms have the same label precisely when no active cut separates them.
Refining the cut state is therefore exactly successive conditioning on the
two observed labels, at the level of normalized probability laws.
-/

@[expose] public section

open scoped BigOperators ENNReal Classical

namespace ExactOverlaps.Poisson

/-- An atom's side of every active cut; inactive cuts contribute `false`. -/
def cutLabel {ι α : Type*} (side : ι → α → Bool) (c : ι → Bool) (a : α) : ι → Bool :=
  fun i ↦ c i && side i a

lemma cutLabel_eq_iff {ι α : Type*} (side : ι → α → Bool) (c : ι → Bool)
    (a b : α) :
    cutLabel side c a = cutLabel side c b ↔
      ∀ i, c i = true → side i a = side i b := by
  constructor
  · intro h i hi
    have hx := congrFun h i
    simpa [cutLabel, hi] using hx
  · intro h
    funext i
    cases hc : c i
    · simp [cutLabel, hc]
    · simp [cutLabel, hc, h i hc]

/-- The finite collection of potential cuts separating two atoms. -/
noncomputable def separatingCuts {ι α : Type*} [Fintype ι] (side : ι → α → Bool)
    (a b : α) : Finset ι := Finset.univ.filter (fun i ↦ side i a ≠ side i b)

lemma cutLabel_eq_iff_no_separating_cut {ι α : Type*} [Fintype ι]
    (side : ι → α → Bool) (c : ι → Bool) (a b : α) :
    cutLabel side c a = cutLabel side c b ↔
      ∀ i ∈ separatingCuts side a b, c i = false := by
  rw [cutLabel_eq_iff]
  constructor
  · intro h i hi
    have hne : side i a ≠ side i b := (Finset.mem_filter.mp hi).2
    cases hc : c i
    · rfl
    · exact (hne (h i hc)).elim
  · intro h i hi
    by_contra hne
    have hz := h i (by simp [separatingCuts, hne])
    simp [hi] at hz

/-- Same-cell probability under the actual finite cut law. -/
lemma cutPMF_same_label {ι α : Type*} [Fintype ι] (d : ι → ℝ)
    (hd : ∀ i, 0 ≤ d i) (t : ℝ) (ht : 0 ≤ t) (side : ι → α → Bool) (a b : α) :
    (∑ c : ι → Bool, if cutLabel side c a = cutLabel side c b
      then (cutPMF d hd t ht c).toReal else 0) =
      Real.exp (-((∑ i ∈ separatingCuts side a b, d i) * t)) := by
  simp only [cutLabel_eq_iff_no_separating_cut]
  exact cutPMF_no_cuts_on d hd t ht (separatingCuts side a b)

/-- A union cell is exactly the intersection of the two component cells. -/
lemma cutLabel_union_eq_iff {ι α : Type*} (side : ι → α → Bool)
    (c c' : ι → Bool) (a b : α) :
    cutLabel side (unionCuts c c') a = cutLabel side (unionCuts c c') b ↔
      cutLabel side c a = cutLabel side c b ∧ cutLabel side c' a = cutLabel side c' b := by
  simp only [cutLabel_eq_iff, unionCuts, Bool.or_eq_true]
  constructor
  · intro h
    exact ⟨fun i hi ↦ h i (Or.inl hi), fun i hi ↦ h i (Or.inr hi)⟩
  · rintro ⟨h, h'⟩ i (hi | hi)
    · exact h i hi
    · exact h' i hi

/-- The actual conditional law in a refined cell is the joint-observation conditional law. -/
lemma conditionalAt_unionCuts {ι α : Type*} (p : PMF α) (side : ι → α → Bool)
    (c c' : ι → Bool) (a : p.support) :
    Entropy.conditionalAt p (cutLabel side (unionCuts c c')) a =
      Entropy.conditionalAt p (fun x ↦ (cutLabel side c x, cutLabel side c' x)) a := by
  apply Entropy.conditionalAt_eq_of_fiber_eq
  intro x
  rw [cutLabel_union_eq_iff, Prod.mk.injEq]

/-- Adding a cut state is exactly conditioning the existing cell on the new label. -/
lemma conditionalAt_unionCuts_eq_successive {ι α : Type*} (p : PMF α)
    (side : ι → α → Bool) (c c' : ι → Bool) (a : p.support) :
    Entropy.conditionalAt p (cutLabel side (unionCuts c c')) a =
      Entropy.conditionalAt (Entropy.conditionalAt p (cutLabel side c) a)
        (cutLabel side c') ⟨a, Entropy.mem_support_conditionalAt p (cutLabel side c) a⟩ := by
  rw [conditionalAt_unionCuts, Entropy.conditionalAt_conditionalAt]

end ExactOverlaps.Poisson
