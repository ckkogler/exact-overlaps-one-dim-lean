module

public import ExactOverlaps.Probability.PoissonCuts
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Probabilities of finite cut patterns

Specifying any subset of gap indicators has the product of its coordinate
probabilities. In particular this proves the finite independence property
needed when identifying a contiguous block as an observed cell.
-/

@[expose] public section

open scoped BigOperators ENNReal Classical

namespace ExactOverlaps.Poisson

lemma sum_cutWeight_pattern {ι : Type*} [Fintype ι] (d : ι → ℝ) (t : ℝ)
    (s : Finset ι) (b : ι → Bool) :
    (∑ c : ι → Bool, if ∀ i ∈ s, c i = b i then cutWeight d t c else 0) =
      ∏ i ∈ s, if b i then 1 - Real.exp (-(d i * t)) else Real.exp (-(d i * t)) := by
  let w (i : ι) (a : Bool) :=
    if a then 1 - Real.exp (-(d i * t)) else Real.exp (-(d i * t))
  let v (i : ι) (a : Bool) := if i ∈ s then (if a = b i then w i a else 0) else w i a
  have hv (c : ι → Bool) :
      (∏ i, v i (c i)) = if ∀ i ∈ s, c i = b i then cutWeight d t c else 0 := by
    by_cases hc : ∀ i ∈ s, c i = b i
    · rw [ite_eq_left hc]
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ s
      · simp [v, hi, hc i hi, w]
      · simp [v, hi, w]
    · rw [ite_eq_right hc]
      obtain ⟨i, hi⟩ := not_forall.mp hc
      obtain ⟨hi, hbi⟩ := not_imp.mp hi
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [v, hi, hbi]
  calc
    (∑ c : ι → Bool, if ∀ i ∈ s, c i = b i then cutWeight d t c else 0) =
        ∑ c : ι → Bool, ∏ i, v i (c i) := by
      apply Finset.sum_congr rfl
      intro c _
      exact (hv c).symm
    _ = ∏ i, ∑ a : Bool, v i a := (Fintype.prod_sum v).symm
    _ = ∏ i, if i ∈ s then w i (b i) else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ s
      · cases hbi : b i <;> simp [v, w, hi, hbi]
      · simp [v, w, hi]
    _ = ∏ i ∈ s, w i (b i) := Finset.prod_ite_mem_eq s _

/-- A partial cut pattern has the product of its prescribed coordinate probabilities. -/
lemma cutPMF_pattern_toReal {ι : Type*} [Fintype ι] (d : ι → ℝ)
    (hd : ∀ i, 0 ≤ d i) (t : ℝ) (ht : 0 ≤ t) (s : Finset ι) (b : ι → Bool) :
    (∑ c : ι → Bool, if ∀ i ∈ s, c i = b i then (cutPMF d hd t ht c).toReal else 0) =
      ∏ i ∈ s, if b i then 1 - Real.exp (-(d i * t)) else Real.exp (-(d i * t)) := by
  simp_rw [cutPMF_toReal]
  exact sum_cutWeight_pattern d t s b

/-- The pattern formula computes the actual probability measure of the event. -/
theorem cutPMF_pattern_measure {ι : Type*} [Fintype ι]
    [MeasurableSpace (ι → Bool)] [MeasurableSingletonClass (ι → Bool)]
    (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) (t : ℝ) (ht : 0 ≤ t)
    (s : Finset ι) (b : ι → Bool) :
    ((cutPMF d hd t ht).toMeasure {c | ∀ i ∈ s, c i = b i}).toReal =
      ∏ i ∈ s, if b i then 1 - Real.exp (-(d i * t)) else Real.exp (-(d i * t)) := by
  rw [PMF.toMeasure_apply_fintype, ENNReal.toReal_sum]
  · simp only [Set.indicator, Set.mem_ofPred_eq]
    simp_rw [apply_ite ENNReal.toReal, ENNReal.toReal_zero]
    refine Eq.trans ?_ (cutPMF_pattern_toReal d hd t ht s b)
    apply Finset.sum_congr rfl
    intro c _
    split_ifs <;> rfl
  · intro c _
    simp only [Set.indicator, Set.mem_ofPred_eq]
    split_ifs
    · exact (cutPMF d hd t ht).apply_ne_top c
    · exact ENNReal.zero_ne_top

/-- No cut in a prescribed set of gaps has the expected exponential probability. -/
lemma cutPMF_no_cuts_on {ι : Type*} [Fintype ι] (d : ι → ℝ)
    (hd : ∀ i, 0 ≤ d i) (t : ℝ) (ht : 0 ≤ t) (s : Finset ι) :
    (∑ c : ι → Bool, if ∀ i ∈ s, c i = false then (cutPMF d hd t ht c).toReal else 0) =
      Real.exp (-((∑ i ∈ s, d i) * t)) := by
  rw [cutPMF_pattern_toReal d hd t ht s (fun _ ↦ false)]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [← Real.exp_sum]
  congr 1
  simp [Finset.sum_neg_distrib, ← Finset.sum_mul]

end ExactOverlaps.Poisson
