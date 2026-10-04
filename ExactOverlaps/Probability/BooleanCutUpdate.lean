module

public import ExactOverlaps.Probability.PoissonCuts
import Mathlib.Tactic.Ring

/-!
# Pairing finite cut states across one coordinate

Flipping a single Boolean coordinate is an involution. Pairing its two
states converts the signed derivative of a Bernoulli weight into the
increment from revealing that coordinate.
-/

@[expose] public section

open scoped BigOperators Classical

namespace ExactOverlaps.Poisson

noncomputable def flipCut {ι : Type*} (i : ι) (c : ι → Bool) : ι → Bool :=
  Function.update c i (!c i)

lemma flipCut_involutive {ι : Type*} (i : ι) : Function.Involutive (flipCut i) := by
  intro c
  funext j
  by_cases hj : j = i
  · subst j
    simp [flipCut]
  · simp [flipCut, Function.update_of_ne hj]

noncomputable def flipCutEquiv {ι : Type*} (i : ι) : (ι → Bool) ≃ (ι → Bool) where
  toFun := flipCut i
  invFun := flipCut i
  left_inv := flipCut_involutive i
  right_inv := flipCut_involutive i

lemma sum_true_cut_eq_sum_false_updated {ι : Type*} [Fintype ι] (i : ι)
    (w f : (ι → Bool) → ℝ)
    (hw : ∀ c b, w (Function.update c i b) = w c) :
    (∑ c : ι → Bool, if c i then w c * f c else 0) =
      ∑ c : ι → Bool, if c i then 0 else w c * f (Function.update c i true) := by
  apply Fintype.sum_equiv (flipCutEquiv i)
  intro c
  change (if c i then w c * f c else 0) =
    if flipCut i c i then 0 else w (flipCut i c) * f (Function.update (flipCut i c) i true)
  cases hc : c i
  · simp [flipCut, hc]
  · have hu : Function.update c i true = c := by
      simpa only [hc] using Function.update_eq_self i c
    simp [flipCut, hc, hw, hu]

lemma sum_signed_cut_eq_increments {ι : Type*} [Fintype ι] (i : ι)
    (w f : (ι → Bool) → ℝ)
    (hw : ∀ c b, w (Function.update c i b) = w c) :
    (∑ c : ι → Bool, w c * (if c i then f c else -f c)) =
      ∑ c : ι → Bool, if c i then 0 else w c * (f (Function.update c i true) - f c) := by
  have hs := sum_true_cut_eq_sum_false_updated i w f hw
  calc
    (∑ c : ι → Bool, w c * (if c i then f c else -f c)) =
      (∑ c : ι → Bool, if c i then w c * f c else 0) -
        ∑ c : ι → Bool, if c i then 0 else w c * f c := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro c _
      cases c i <;> simp
    _ = _ := by
      rw [hs, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro c _
      cases c i <;> simp [mul_sub]

end ExactOverlaps.Poisson
