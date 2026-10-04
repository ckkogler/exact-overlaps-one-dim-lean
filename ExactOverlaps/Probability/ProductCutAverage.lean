module

public import ExactOverlaps.Probability.PoissonCuts
public import Mathlib.Logic.Equiv.Prod

/-!
# Marginal averages for independent families of cuts

The cut weights on a product index set factor into the coordinate cut
weights. An observable depending on one coordinate family therefore has
exactly its marginal average, including at time zero.
-/

@[expose] public section

open scoped BigOperators Classical

namespace ExactOverlaps.Poisson

lemma sum_product_weight_coordinate {ι α : Type*} [Fintype ι] [Fintype α]
    (w : ι → α → ℝ) (hw : ∀ i, ∑ a, w i a = 1) (i : ι) (F : α → ℝ) :
    (∑ f : ι → α, (∏ j, w j (f j)) * F (f i)) = ∑ a, w i a * F a := by
  have h (f : ι → α) : (∏ j, w j (f j)) * F (f i) =
      ∏ j, w j (f j) * (if j = i then F (f j) else 1) := by
    rw [Finset.prod_mul_distrib]
    simp
  simp_rw [h]
  rw [← Fintype.prod_sum (fun j a ↦ w j a * (if j = i then F a else 1))]
  have hs (j : ι) : (∑ a, w j a * (if j = i then F a else 1)) =
      if j = i then ∑ a, w i a * F a else 1 := by
    by_cases hj : j = i
    · subst j
      simp
    · simp [hj, hw]
  simp_rw [hs]
  simp

lemma cutWeight_product {ι κ : Type*} [Fintype ι] [Fintype κ]
    (d : ι × κ → ℝ) (t : ℝ) (c : ι × κ → Bool) :
    cutWeight d t c = ∏ i, cutWeight (fun j ↦ d (i, j)) t (fun j ↦ c (i, j)) := by
  simp only [cutWeight, Fintype.prod_prod_type]

theorem sum_cutWeight_coordinate {ι κ : Type*} [Fintype ι] [Fintype κ]
    (d : ι × κ → ℝ) (t : ℝ) (i : ι) (F : (κ → Bool) → ℝ) :
    (∑ c : ι × κ → Bool, cutWeight d t c * F (fun j ↦ c (i, j))) =
      ∑ c : κ → Bool, cutWeight (fun j ↦ d (i, j)) t c * F c := by
  calc
    _ = ∑ c : ι → κ → Bool, (∏ j, cutWeight (fun k ↦ d (j, k)) t (c j)) * F (c i) := by
      apply Fintype.sum_equiv (Equiv.curry ι κ Bool)
      intro c
      rw [cutWeight_product]
      rfl
    _ = _ := sum_product_weight_coordinate
      (fun j c ↦ cutWeight (fun k ↦ d (j, k)) t c)
      (fun j ↦ sum_cutWeight (fun k ↦ d (j, k)) t) i F

end ExactOverlaps.Poisson
