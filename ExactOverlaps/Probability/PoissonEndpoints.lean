module

public import ExactOverlaps.Probability.PoissonGenerator
public import Mathlib.Order.Filter.AtTopBot.Field

/-!
# Initial and terminal finite Poisson cut laws

At intensity zero no gap is cut. When every gap has positive length, the
finite cut law converges to the state with every gap cut. Finite averages
therefore have their actual initial and terminal values.
-/

@[expose] public section

open Filter
open scoped BigOperators Topology Classical

namespace ExactOverlaps.Poisson

lemma prod_bool_indicator {ι : Type*} [Fintype ι] (c : ι → Bool) (b : Bool) :
    (∏ i, if c i = b then (1 : ℝ) else 0) = if c = (fun _ ↦ b) then 1 else 0 := by
  by_cases hc : c = (fun _ ↦ b)
  · simp [hc]
  · rw [ite_eq_right hc]
    obtain ⟨i, hi⟩ := not_forall.mp (show ¬∀ i, c i = b from fun h ↦ hc (funext h))
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

lemma cutWeight_zero {ι : Type*} [Fintype ι] (d : ι → ℝ) (c : ι → Bool) :
    cutWeight d 0 c = if c = (fun _ ↦ false) then 1 else 0 := by
  have he : cutWeight d 0 c = ∏ i, if c i = false then (1 : ℝ) else 0 := by
    apply Finset.prod_congr rfl
    intro i _
    cases c i <;> simp
  rw [he, prod_bool_indicator]

lemma cutAverage_zero {ι : Type*} [Fintype ι] (d : ι → ℝ) (f : (ι → Bool) → ℝ) :
    cutAverage d f 0 = f (fun _ ↦ false) := by
  simp [cutAverage, cutWeight_zero]

lemma tendsto_gap_survival_zero {d : ℝ} (hd : 0 < d) :
    Tendsto (fun t : ℝ ↦ Real.exp (-(d * t))) atTop (𝓝 0) := by
  have h := tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hd)
  have he := Real.tendsto_exp_atBot.comp h
  simpa only [Function.comp_def, neg_mul, id_eq] using he

lemma tendsto_cutWeight {ι : Type*} [Fintype ι] (d : ι → ℝ)
    (hd : ∀ i, 0 < d i) (c : ι → Bool) :
    Tendsto (fun t ↦ cutWeight d t c) atTop (𝓝 (if c = (fun _ ↦ true) then 1 else 0)) := by
  rw [← prod_bool_indicator c true]
  apply tendsto_finsetProd
  intro i _
  cases hc : c i
  · simpa only [hc, Bool.false_eq_true, ite_false] using tendsto_gap_survival_zero (hd i)
  · simpa only [hc, ite_true, sub_zero] using tendsto_const_nhds.sub (tendsto_gap_survival_zero (hd i))

theorem tendsto_cutAverage {ι : Type*} [Fintype ι] (d : ι → ℝ)
    (hd : ∀ i, 0 < d i) (f : (ι → Bool) → ℝ) :
    Tendsto (cutAverage d f) atTop (𝓝 (f (fun _ ↦ true))) := by
  unfold cutAverage
  have h := tendsto_finsetSum Finset.univ
    (fun c _ ↦ (tendsto_cutWeight d hd c).mul_const (f c))
  simpa using h

end ExactOverlaps.Poisson
