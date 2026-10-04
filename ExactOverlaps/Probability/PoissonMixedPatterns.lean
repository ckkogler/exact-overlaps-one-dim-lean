module

public import ExactOverlaps.Probability.PoissonPatterns

/-!
# Independent cut and no-cut constraints

Disjoint sets of gaps may be prescribed uncut and cut. The exact finite
probability is the exponential survival of the first set times the product
of the cut probabilities of the second set.
-/

@[expose] public section

open scoped BigOperators Classical

namespace ExactOverlaps.Poisson

lemma sum_cutWeight_mixedPattern {ι : Type*} [Fintype ι] (d : ι → ℝ) (t : ℝ)
    (s₀ s₁ : Finset ι) (hs : Disjoint s₀ s₁) :
    (∑ c : ι → Bool, if (∀ i ∈ s₀, c i = false) ∧ (∀ i ∈ s₁, c i = true)
      then cutWeight d t c else 0) =
      Real.exp (-((∑ i ∈ s₀, d i) * t)) *
        ∏ i ∈ s₁, (1 - Real.exp (-(d i * t))) := by
  let b : ι → Bool := fun i ↦ decide (i ∈ s₁)
  have hb₀ (i : ι) (hi : i ∈ s₀) : b i = false := by
    have hn : i ∉ s₁ := Finset.disjoint_left.mp hs hi
    simp [b, hn]
  have hb₁ (i : ι) (hi : i ∈ s₁) : b i = true := by simp [b, hi]
  have he (c : ι → Bool) :
      ((∀ i ∈ s₀, c i = false) ∧ (∀ i ∈ s₁, c i = true)) ↔
        ∀ i ∈ s₀ ∪ s₁, c i = b i := by
    constructor
    · rintro ⟨h₀, h₁⟩ i hi
      rcases Finset.mem_union.mp hi with hi | hi
      · rw [h₀ i hi, hb₀ i hi]
      · rw [h₁ i hi, hb₁ i hi]
    · intro h
      constructor
      · intro i hi
        rw [h i (Finset.mem_union_left _ hi), hb₀ i hi]
      · intro i hi
        rw [h i (Finset.mem_union_right _ hi), hb₁ i hi]
  calc
    (∑ c : ι → Bool, if (∀ i ∈ s₀, c i = false) ∧ (∀ i ∈ s₁, c i = true)
        then cutWeight d t c else 0) =
        ∑ c : ι → Bool, if ∀ i ∈ s₀ ∪ s₁, c i = b i then cutWeight d t c else 0 := by
      simp only [he]
    _ = ∏ i ∈ s₀ ∪ s₁, if b i then 1 - Real.exp (-(d i * t)) else Real.exp (-(d i * t)) :=
      sum_cutWeight_pattern d t (s₀ ∪ s₁) b
    _ = (∏ i ∈ s₀, Real.exp (-(d i * t))) *
        ∏ i ∈ s₁, (1 - Real.exp (-(d i * t))) := by
      rw [Finset.prod_union hs]
      congr 1
      · apply Finset.prod_congr rfl
        intro i hi
        simp [hb₀ i hi]
      · apply Finset.prod_congr rfl
        intro i hi
        simp [hb₁ i hi]
    _ = _ := by
      rw [← Real.exp_sum]
      congr 2
      simp [Finset.sum_neg_distrib, ← Finset.sum_mul]

end ExactOverlaps.Poisson
