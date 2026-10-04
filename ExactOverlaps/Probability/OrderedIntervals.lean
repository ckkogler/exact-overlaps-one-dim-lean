module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
# Integrating constants over successive finite grid gaps

Consecutive half-open intervals in an increasing grid are disjoint. Their
length-weighted constant values sum to the integral over their union, and
are bounded by a nonnegative integrable majorant on the whole real line.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators Classical

namespace ExactOverlaps.FiniteProbability

lemma pairwise_disjoint_grid_gaps {n : ℕ} (x : ℕ → ℝ)
    (hx : Monotone (fun a : Fin (n + 1) ↦ x a.val)) :
    Pairwise (fun i j : Fin n ↦ Disjoint (Ico (x i.val) (x (i.val + 1)))
      (Ico (x j.val) (x (j.val + 1)))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro a hai haj
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have h : x (i.val + 1) ≤ x j.val :=
      hx (show (i.succ : Fin (n + 1)) ≤ j.castSucc by exact_mod_cast Nat.succ_le_of_lt hlt)
    exact (not_lt_of_ge (h.trans haj.1)) hai.2
  · have h : x (j.val + 1) ≤ x i.val :=
      hx (show (j.succ : Fin (n + 1)) ≤ i.castSucc by exact_mod_cast Nat.succ_le_of_lt hgt)
    exact (not_lt_of_ge (h.trans hai.1)) haj.2

theorem sum_gap_mul_le_integral {n : ℕ} (x : ℕ → ℝ)
    (hx : Monotone (fun a : Fin (n + 1) ↦ x a.val)) (c : Fin n → ℝ)
    (f : ℝ → ℝ) (hi : Integrable f) (hn : ∀ a, 0 ≤ f a)
    (hc : ∀ j : Fin n, ∀ a ∈ Ico (x j.val) (x (j.val + 1)), f a = c j) :
    (∑ j : Fin n, (x (j.val + 1) - x j.val) * c j) ≤ ∫ a, f a := by
  have he (j : Fin n) : (∫ a in Ico (x j.val) (x (j.val + 1)), f a) =
      (x (j.val + 1) - x j.val) * c j := by
    rw [setIntegral_congr_fun measurableSet_Ico (hc j)]
    rw [integral_const]
    have hxj : x j.val ≤ x (j.val + 1) :=
      hx (show j.castSucc ≤ j.succ by exact_mod_cast Nat.le_succ j.val)
    simp [Measure.real, Real.volume_Ico, ENNReal.toReal_ofReal (sub_nonneg.mpr hxj), smul_eq_mul]
  have hU := integral_iUnion_fintype
    (fun j : Fin n ↦ measurableSet_Ico (a := x j.val) (b := x (j.val + 1)))
    (pairwise_disjoint_grid_gaps x hx) (fun _ ↦ hi.integrableOn)
  simp_rw [he] at hU
  rw [← hU]
  exact setIntegral_le_integral hi (Filter.Eventually.of_forall hn)

end ExactOverlaps.FiniteProbability
