module

public import ExactOverlaps.Entropy.Bounds
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Cross-entropy bounds for finite prediction

A predictor may assign probability zero to an event only when that event has
probability zero under the true law. This formulation includes deterministic
binary outcomes without treating the totalized real logarithm at zero as a
finite loss for a positive-probability event.
-/

@[expose] public section

open scoped BigOperators

namespace ExactOverlaps.Entropy

lemma negMulLog_le_crossEntropy_term {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hsupport : p ≠ 0 → q ≠ 0) :
    Real.negMulLog p ≤ p * (-Real.log q) + q - p := by
  by_cases hp0 : p = 0
  · simpa [hp0] using hq
  · have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
    have hq' : 0 < q := lt_of_le_of_ne hq (Ne.symm (hsupport hp0))
    have h := negMulLog_le_log_bound hp' (inv_pos.mpr hq')
    simpa only [Real.log_inv, one_div, inv_inv] using h

/-- Gibbs' inequality for finite subprobability predictors, including null atoms. -/
theorem finite_entropy_le_crossEntropy {ι : Type*} (s : Finset ι)
    (p q : ι → ℝ) (hp : ∀ i ∈ s, 0 ≤ p i) (hq : ∀ i ∈ s, 0 ≤ q i)
    (hpsum : ∑ i ∈ s, p i = 1) (hqsum : ∑ i ∈ s, q i ≤ 1)
    (hsupport : ∀ i ∈ s, p i ≠ 0 → q i ≠ 0) :
    ∑ i ∈ s, Real.negMulLog (p i) ≤ ∑ i ∈ s, p i * (-Real.log (q i)) := by
  have h := Finset.sum_le_sum (fun i hi ↦
    negMulLog_le_crossEntropy_term (hp i hi) (hq i hi) (hsupport i hi))
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hpsum] at h
  linarith

/-- The entropy of a binary outcome is bounded by the logarithmic loss of a predictor. -/
theorem binEntropy_le_crossEntropy {p q : ℝ} (hp : p ∈ Set.Icc 0 1)
    (hq : q ∈ Set.Icc 0 1) (hzero : p ≠ 0 → q ≠ 0) (hone : p ≠ 1 → q ≠ 1) :
    Real.binEntropy p ≤ p * (-Real.log q) + (1 - p) * (-Real.log (1 - q)) := by
  have h₀ := negMulLog_le_crossEntropy_term hp.1 hq.1 hzero
  have h₁ := negMulLog_le_crossEntropy_term (sub_nonneg.mpr hp.2)
    (sub_nonneg.mpr hq.2) (by
      intro h
      apply sub_ne_zero.mpr
      exact Ne.symm (hone (fun hp1 ↦ h (by rw [hp1]; ring))))
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  linarith

/-- A convenient elementary estimate for the loss of the product predictor. -/
lemma log_one_add_le_sqrt {z : ℝ} (hz : 0 ≤ z) : Real.log (1 + z) ≤ Real.sqrt z := by
  have ht := Real.sum_le_exp_of_nonneg (Real.sqrt_nonneg z) 4
  norm_num [Finset.sum_range_succ] at ht
  have hs := Real.sq_sqrt hz
  have hpoly := mul_nonneg (Real.sqrt_nonneg z) (sq_nonneg (Real.sqrt z - 3 / 2))
  apply (Real.log_le_iff_le_exp (by linarith : 0 < 1 + z)).mpr
  nlinarith [Real.sqrt_nonneg z]

/-- A mass increment is bounded by twice the increment of its cumulative square root. -/
lemma div_sqrt_add_le_sqrt_sub {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    b / Real.sqrt (a + b) ≤ 2 * (Real.sqrt (a + b) - Real.sqrt a) := by
  by_cases hab : a + b = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [ha0, hb0]
  · have habpos : 0 < a + b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hab)
    apply (div_le_iff₀ (Real.sqrt_pos.mpr habpos)).mpr
    have h₀ := Real.sq_sqrt ha
    have h₁ := Real.sq_sqrt habpos.le
    nlinarith [sq_nonneg (Real.sqrt (a + b) - Real.sqrt a)]

/-- The finite quantile estimate, obtained by telescoping cumulative square roots. -/
lemma sum_div_sqrt_cumulative_le (w : ℕ → ℝ) (n : ℕ)
    (hw : ∀ i < n, 0 ≤ w i) :
    (∑ i ∈ Finset.range n, w i / Real.sqrt (∑ j ∈ Finset.range (i + 1), w j)) ≤
      2 * Real.sqrt (∑ i ∈ Finset.range n, w i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hw' : ∀ i < n, 0 ≤ w i := fun i hi ↦ hw i (Nat.lt_trans hi (Nat.lt_succ_self n))
    have hn : 0 ≤ w n := hw n (Nat.lt_succ_self n)
    have hs : 0 ≤ ∑ i ∈ Finset.range n, w i :=
      Finset.sum_nonneg (fun i hi ↦ hw' i (Finset.mem_range.mp hi))
    calc
      (∑ i ∈ Finset.range (n + 1),
          w i / Real.sqrt (∑ j ∈ Finset.range (i + 1), w j)) =
          (∑ i ∈ Finset.range n, w i / Real.sqrt (∑ j ∈ Finset.range (i + 1), w j)) +
            w n / Real.sqrt ((∑ j ∈ Finset.range n, w j) + w n) := by
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
      _ ≤ 2 * Real.sqrt (∑ i ∈ Finset.range n, w i) +
          2 * (Real.sqrt ((∑ i ∈ Finset.range n, w i) + w n) -
            Real.sqrt (∑ i ∈ Finset.range n, w i)) :=
        add_le_add (ih hw') (div_sqrt_add_le_sqrt_sub hs hn)
      _ = 2 * Real.sqrt (∑ i ∈ Finset.range (n + 1), w i) := by
        rw [Finset.sum_range_succ]
        ring

end ExactOverlaps.Entropy
