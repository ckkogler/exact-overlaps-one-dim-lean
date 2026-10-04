module

public import ExactOverlaps.Probability.PoissonPatterns
import Mathlib.Tactic.Ring

/-!
# Independent refinement of finite Poisson cut states

Independent cut states at intensities `t` and `u` combine by taking the
coordinatewise union. Their union has exactly the cut-state law at intensity
`t+u`. This is the finite observation form of superposition of Poisson cuts.
-/

@[expose] public section

open scoped BigOperators ENNReal Classical

namespace ExactOverlaps.Poisson

/-- Probability weight of one gap indicator. -/
noncomputable def cutCoordinateWeight (d t : ℝ) (c : Bool) : ℝ :=
  if c then 1 - Real.exp (-(d * t)) else Real.exp (-(d * t))

/-- Union of the sets of gaps cut by two independent observations. -/
def unionCuts {ι : Type*} (c c' : ι → Bool) : ι → Bool := fun i ↦ c i || c' i

lemma cutCoordinateWeight_union_sum (d t u : ℝ) (z : Bool) :
    (∑ a : Bool, ∑ b : Bool,
      if (a || b) = z then cutCoordinateWeight d t a * cutCoordinateWeight d u b else 0) =
      cutCoordinateWeight d (t + u) z := by
  cases z
  · simp [cutCoordinateWeight, survival_add_time]
  · simp [cutCoordinateWeight, survival_add_time]
    ring

/-- Finite product weights obey the exact union convolution law. -/
lemma sum_cutWeight_union {ι : Type*} [Fintype ι] (d : ι → ℝ) (t u : ℝ)
    (z : ι → Bool) :
    (∑ c : ι → Bool, ∑ c' : ι → Bool,
      if unionCuts c c' = z then cutWeight d t c * cutWeight d u c' else 0) =
      cutWeight d (t + u) z := by
  let K (i : ι) (a b : Bool) :=
    if (a || b) = z i then cutCoordinateWeight (d i) t a * cutCoordinateWeight (d i) u b else 0
  have hprod (c c' : ι → Bool) :
      (∏ i, K i (c i) (c' i)) =
        if unionCuts c c' = z then cutWeight d t c * cutWeight d u c' else 0 := by
    simp only [K, Finset.prod_ite_zero, Finset.mem_univ, forall_const,
      Finset.prod_mul_distrib]
    by_cases h : unionCuts c c' = z
    · have hx : ∀ i, (c i || c' i) = z i := fun i ↦ congrFun h i
      simp [hx, h, cutWeight, cutCoordinateWeight]
    · have hx : ¬ ∀ i, (c i || c' i) = z i := fun hx ↦ h (funext hx)
      simp [hx, h]
  calc
    (∑ c : ι → Bool, ∑ c' : ι → Bool,
        if unionCuts c c' = z then cutWeight d t c * cutWeight d u c' else 0) =
        ∑ c : ι → Bool, ∑ c' : ι → Bool, ∏ i, K i (c i) (c' i) := by
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro c' _
      exact (hprod c c').symm
    _ = ∑ c : ι → Bool, ∏ i, ∑ b : Bool, K i (c i) b := by
      apply Finset.sum_congr rfl
      intro c _
      exact (Fintype.prod_sum (fun i b ↦ K i (c i) b)).symm
    _ = ∏ i, ∑ a : Bool, ∑ b : Bool, K i a b :=
      (Fintype.prod_sum (fun i a ↦ ∑ b : Bool, K i a b)).symm
    _ = ∏ i, cutCoordinateWeight (d i) (t + u) (z i) := by
      apply Finset.prod_congr rfl
      intro i _
      exact cutCoordinateWeight_union_sum (d i) t u (z i)
    _ = cutWeight d (t + u) z := rfl

/-- The law obtained by independently adding a fresh cut state. -/
noncomputable def refinedCutPMF {ι : Type*} [Fintype ι] (d : ι → ℝ)
    (hd : ∀ i, 0 ≤ d i) (t : ℝ) (ht : 0 ≤ t) (u : ℝ) (hu : 0 ≤ u) : PMF (ι → Bool) :=
  (cutPMF d hd t ht).bind (fun c ↦ (cutPMF d hd u hu).map (unionCuts c))

lemma refinedCutPMF_toReal {ι : Type*} [Fintype ι] (d : ι → ℝ)
    (hd : ∀ i, 0 ≤ d i) (t : ℝ) (ht : 0 ≤ t) (u : ℝ) (hu : 0 ≤ u)
    (z : ι → Bool) :
    (refinedCutPMF d hd t ht u hu z).toReal =
      ∑ c : ι → Bool, ∑ c' : ι → Bool,
        if unionCuts c c' = z then cutWeight d t c * cutWeight d u c' else 0 := by
  rw [refinedCutPMF, PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro c _
    rw [ENNReal.toReal_mul, PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
    · rw [Finset.mul_sum, cutPMF_toReal]
      apply Finset.sum_congr rfl
      intro c' _
      by_cases h : unionCuts c c' = z
      · simp [h, cutWeight_nonneg d hd hu]
      · simp [h, Ne.symm h]
    · intro c' _
      split_ifs <;> simp
  · intro c _
    exact ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)

/-- Independent refinement agrees with the actual probability law at total intensity. -/
lemma refinedCutPMF_eq {ι : Type*} [Fintype ι] (d : ι → ℝ)
    (hd : ∀ i, 0 ≤ d i) (t : ℝ) (ht : 0 ≤ t) (u : ℝ) (hu : 0 ≤ u) :
    refinedCutPMF d hd t ht u hu = cutPMF d hd (t + u) (add_nonneg ht hu) := by
  ext z
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [refinedCutPMF_toReal, cutPMF_toReal, sum_cutWeight_union]

end ExactOverlaps.Poisson
