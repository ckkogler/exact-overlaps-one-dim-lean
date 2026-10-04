/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic

/-! The exact geometric cost bound used when concatenating uniformly improving blocks. -/

@[expose] public section

open Filter
open scoped Topology BigOperators

namespace ExactOverlaps.MainTheorem

theorem product_rpow_le_exp {n : ℕ} (v : Fin n → ℝ) (κ a : ℝ)
    (ha : 0 ≤ a) (hv : ∀ j, 0 ≤ v j) (hcap : ∀ j, v j ≤ Real.exp (-κ)) :
    (∏ j, (v j) ^ a) ≤ Real.exp (-((n : ℝ) * κ * a)) := by
  calc
    (∏ j, (v j) ^ a) ≤ ∏ _j : Fin n, (Real.exp (-κ)) ^ a := by
      apply Finset.prod_le_prod₀
      · intro j _
        exact Real.rpow_nonneg (hv j) a
      · intro j _
        exact Real.rpow_le_rpow (hv j) (hcap j) ha
    _ = Real.exp (-((n : ℝ) * κ * a)) := by
      simp only [← Real.exp_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [← Real.exp_nat_mul]
      congr 1
      ring

theorem tendsto_zero_of_exponential_cost_bound (f : ℕ → ℝ) {κ a : ℝ}
    (hκ : 0 < κ) (ha : 0 < a) (hf : ∀ n, 0 ≤ f n)
    (hbound : ∀ n, f n ≤ Real.exp (-((n : ℝ) * κ * a))) :
    Tendsto f atTop (𝓝 0) := by
  have hbase : 0 < Real.exp (-(κ * a)) := Real.exp_pos _
  have hlt : Real.exp (-(κ * a)) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos hκ ha))
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hbase.le hlt
  have he (n : ℕ) : Real.exp (-((n : ℝ) * κ * a)) = Real.exp (-(κ * a)) ^ n := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  exact squeeze_zero hf (fun n ↦ by rw [← he]; exact hbound n) hp

end ExactOverlaps.MainTheorem
