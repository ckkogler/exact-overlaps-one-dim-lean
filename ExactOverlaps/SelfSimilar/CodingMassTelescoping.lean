module

public import ExactOverlaps.SelfSimilar.CodingBallMass
public import ExactOverlaps.SelfSimilar.CodingSymbolInformation

/-!
Exact logarithmic ball-mass telescoping along signed affine coding. The
identity is asserted on positive-weight, positive-ball-mass orbits, and
retains the initial-radius terminal term explicitly.
-/

@[expose] public section

open MeasureTheory Filter Metric
open scoped ENNReal Topology

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem log_prefixBallMass_succ (S : System ι) (r : ℝ) (n : ℕ) (ω : ℕ → ι)
    (hw : (S.weight (ω 0) : ℝ) ≠ 0)
    (hc : 0 < S.prefixBallMass r (n + 1) ω)
    (ht : 0 < S.prefixBallMass r n (Bernoulli.shift ω)) :
    Real.log (S.prefixBallMass r (n + 1) ω).toReal = S.headLogWeight ω +
      S.prefixBranchInformation r (n + 1) ω +
        Real.log (S.prefixBallMass r n (Bernoulli.shift ω)).toReal := by
  have hc' := (ENNReal.toReal_pos hc.ne' (S.prefixBallMass_ne_top r (n + 1) ω)).ne'
  have ht' := (ENNReal.toReal_pos ht.ne' (S.prefixBallMass_ne_top r n (Bernoulli.shift ω))).ne'
  have heq : S.prefixBranchInformation r (n + 1) ω =
      -Real.log (((S.weight (ω 0) : ℝ≥0∞) * S.prefixBallMass r n (Bernoulli.shift ω)) /
        S.prefixBallMass r (n + 1) ω).toReal := by
    unfold prefixBranchInformation branchBallInformation
    rw [branch_prefixBallMass]
    rfl
  rw [heq, ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.coe_toReal,
    Real.log_div (mul_ne_zero hw ht') hc', Real.log_mul hw ht']
  unfold headLogWeight
  ring

omit [MeasurableSingletonClass ι] in
theorem prefixInformation_sum_succ (S : System ι) (r : ℝ) (n : ℕ) (ω : ℕ → ι) :
    (∑ j ∈ Finset.range (n + 1),
      S.prefixBranchInformation r (n + 1 - j) (Bernoulli.shift^[j] ω)) =
      S.prefixBranchInformation r (n + 1) ω +
        ∑ j ∈ Finset.range n,
          S.prefixBranchInformation r (n - j) (Bernoulli.shift^[j] (Bernoulli.shift ω)) := by
  rw [Finset.sum_range_succ']
  simp only [Nat.sub_zero, Function.iterate_zero_apply, Nat.add_sub_add_right,
    Function.iterate_succ_apply]
  ring

theorem log_prefixBallMass_telescoping (S : System ι) (r : ℝ) (n : ℕ) (ω : ℕ → ι)
    (hw : ∀ j, (S.weight ((Bernoulli.shift^[j] ω) 0) : ℝ) ≠ 0)
    (hm : ∀ j k, 0 < S.prefixBallMass r k (Bernoulli.shift^[j] ω)) :
    Real.log (S.prefixBallMass r n ω).toReal =
      birkhoffSum Bernoulli.shift S.headLogWeight n ω +
        (∑ j ∈ Finset.range n, S.prefixBranchInformation r (n - j) (Bernoulli.shift^[j] ω)) +
          Real.log (S.prefixBallMass r 0 (Bernoulli.shift^[n] ω)).toReal := by
  induction n generalizing ω with
  | zero => simp
  | succ n ih =>
      have hws : ∀ j, (S.weight ((Bernoulli.shift^[j] (Bernoulli.shift ω)) 0) : ℝ) ≠ 0 := by
        intro j
        simpa only [Function.iterate_succ_apply] using hw (j + 1)
      have hms : ∀ j k, 0 < S.prefixBallMass r k (Bernoulli.shift^[j] (Bernoulli.shift ω)) := by
        intro j k
        simpa only [Function.iterate_succ_apply] using hm (j + 1) k
      have hstep := S.log_prefixBallMass_succ r n ω (by simpa using hw 0)
        (by simpa using hm 0 (n + 1)) (by simpa using hm 1 n)
      rw [ih (Bernoulli.shift ω) hws hms] at hstep
      rw [prefixInformation_sum_succ, birkhoffSum_succ_apply', Function.iterate_succ_apply]
      linarith only [hstep]

end ExactOverlaps.SelfSimilar.System
