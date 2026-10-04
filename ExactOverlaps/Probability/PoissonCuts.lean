module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-!
# The finite observation law of Poisson cuts

For a finite support, only the gaps between consecutive atoms matter. At
intensity `t`, a gap of length `d` is uncut with probability `exp(-d*t)`.
The finite product below is a genuine probability mass function on cut
states, including intensity zero. A `true` coordinate means that its gap
has received a cut.
-/

@[expose] public section

open scoped BigOperators ENNReal Classical

namespace ExactOverlaps.Poisson

/-- Weight of a specified finite cut state. -/
noncomputable def cutWeight {ι : Type*} [Fintype ι] (d : ι → ℝ)
    (t : ℝ) (c : ι → Bool) : ℝ :=
  ∏ i, if c i then 1 - Real.exp (-(d i * t)) else Real.exp (-(d i * t))

lemma survival_mem_unit_interval {d t : ℝ} (hd : 0 ≤ d) (ht : 0 ≤ t) :
    Real.exp (-(d * t)) ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨(Real.exp_pos _).le,
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hd ht))⟩

lemma cutWeight_nonneg {ι : Type*} [Fintype ι] (d : ι → ℝ)
    (hd : ∀ i, 0 ≤ d i) {t : ℝ} (ht : 0 ≤ t) (c : ι → Bool) :
    0 ≤ cutWeight d t c := by
  unfold cutWeight
  apply Finset.prod_nonneg
  intro i _
  split_ifs
  · exact sub_nonneg.mpr (survival_mem_unit_interval (hd i) ht).2
  · exact (Real.exp_pos _).le

lemma sum_cutWeight {ι : Type*} [Fintype ι] (d : ι → ℝ) (t : ℝ) :
    ∑ c : ι → Bool, cutWeight d t c = 1 := by
  classical
  unfold cutWeight
  rw [← Fintype.prod_sum (fun i (b : Bool) ↦
    if b then 1 - Real.exp (-(d i * t)) else Real.exp (-(d i * t)))]
  simp

/-- The product law of the gap-cut indicators. -/
noncomputable def cutPMF {ι : Type*} [Fintype ι] (d : ι → ℝ)
    (hd : ∀ i, 0 ≤ d i) (t : ℝ) (ht : 0 ≤ t) : PMF (ι → Bool) :=
  PMF.ofFintype (fun c ↦ ENNReal.ofReal (cutWeight d t c)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun c _ ↦ cutWeight_nonneg d hd ht c),
      sum_cutWeight, ENNReal.ofReal_one])

@[simp] lemma cutPMF_apply {ι : Type*} [Fintype ι] (d : ι → ℝ)
    (hd : ∀ i, 0 ≤ d i) (t : ℝ) (ht : 0 ≤ t) (c : ι → Bool) :
    cutPMF d hd t ht c = ENNReal.ofReal (cutWeight d t c) := rfl

@[simp] lemma cutPMF_toReal {ι : Type*} [Fintype ι] (d : ι → ℝ)
    (hd : ∀ i, 0 ≤ d i) (t : ℝ) (ht : 0 ≤ t) (c : ι → Bool) :
    (cutPMF d hd t ht c).toReal = cutWeight d t c := by
  rw [cutPMF_apply, ENNReal.toReal_ofReal (cutWeight_nonneg d hd ht c)]

/-- The empty cut state has the exponential survival probability of the total gap length. -/
lemma cutWeight_no_cuts {ι : Type*} [Fintype ι] (d : ι → ℝ) (t : ℝ) :
    cutWeight d t (fun _ ↦ false) = Real.exp (-((∑ i, d i) * t)) := by
  simp only [cutWeight, Bool.false_eq_true, ↓reduceIte]
  rw [← Real.exp_sum]
  congr 1
  simp [Finset.sum_neg_distrib, ← Finset.sum_mul]

/-- A positive-length gap is uncut precisely with exponential decay in intensity. -/
lemma survival_add_time (d t u : ℝ) :
    Real.exp (-(d * (t + u))) = Real.exp (-(d * t)) * Real.exp (-(d * u)) := by
  rw [mul_add, neg_add, Real.exp_add]

end ExactOverlaps.Poisson
