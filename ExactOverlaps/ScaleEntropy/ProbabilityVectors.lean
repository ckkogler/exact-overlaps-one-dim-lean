/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.Entropy.ConditionalMixture
public import Mathlib.Analysis.Convex.Integral

/-!
# Finite probability vectors and continuous conditional entropy

Probability vectors have nonnegative coordinates with total mass one.
They are identified with actual PMFs. Conditional entropy is a continuous
function of the vector, written as fine entropy minus coarse entropy.
This presentation permits integral Jensen without restricting the mixing law
to finite support.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical

namespace ExactOverlaps.ProbabilityVectors

open Entropy

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The usual closed finite-dimensional probability simplex. -/
def simplex (α : Type*) [Fintype α] : Set (α → ℝ) :=
  {x | (∀ a, 0 ≤ x a) ∧ ∑ a, x a = 1}

lemma convex_simplex : Convex ℝ (simplex α) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i ↦ add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i)), ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, hx.2, hy.2, mul_one, hab]

lemma isClosed_simplex : IsClosed (simplex α) := by
  have heq : simplex α = (⋂ a, {x : α → ℝ | 0 ≤ x a}) ∩ {x | ∑ a, x a = 1} := by
    ext x
    simp [simplex]
  rw [heq]
  exact (isClosed_iInter (fun a ↦ isClosed_le continuous_const (continuous_apply a))).inter
    (isClosed_eq (by fun_prop) continuous_const)

lemma coordinate_mem_Icc {x : α → ℝ} (hx : x ∈ simplex α) (a : α) : x a ∈ Icc 0 1 := by
  refine ⟨hx.1 a, ?_⟩
  have h := Finset.single_le_sum (fun b _ ↦ hx.1 b) (Finset.mem_univ a)
  simpa only [hx.2] using h

/-- A real probability vector gives an actual probability mass function. -/
def ofVector (x : α → ℝ) (hx : x ∈ simplex α) : PMF α :=
  PMF.ofFintype (fun a ↦ ENNReal.ofReal (x a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ ↦ hx.1 a), hx.2, ENNReal.ofReal_one])

lemma ofVector_toReal (x : α → ℝ) (hx : x ∈ simplex α) (a : α) :
    (ofVector x hx a).toReal = x a := by
  simp only [ofVector, PMF.ofFintype_apply, ENNReal.toReal_ofReal (hx.1 a)]

def vectorOfPMF (p : PMF α) : α → ℝ := fun a ↦ (p a).toReal

lemma vectorOfPMF_mem_simplex (p : PMF α) : vectorOfPMF p ∈ simplex α :=
  ⟨fun _ ↦ ENNReal.toReal_nonneg, sum_pmf_toReal p⟩

lemma vectorOfPMF_ofVector (x : α → ℝ) (hx : x ∈ simplex α) :
    vectorOfPMF (ofVector x hx) = x := by
  funext a
  exact ofVector_toReal x hx a

/-- Natural-logarithmic entropy, as a continuous function of the mass vector. -/
def entropyVector (x : α → ℝ) : ℝ := ∑ a, Real.negMulLog (x a)

@[fun_prop] lemma continuous_entropyVector : Continuous (entropyVector : (α → ℝ) → ℝ) := by
  unfold entropyVector
  fun_prop

/-- Sum fine-label masses along the fibers of the coarse label. -/
def coarseVector (f : α → β) (x : α → ℝ) : β → ℝ :=
  fun b ↦ ∑ a, if f a = b then x a else 0

omit [Fintype β] in
@[fun_prop] lemma continuous_coarseVector (f : α → β) : Continuous (coarseVector f) := by
  unfold coarseVector
  apply continuous_pi
  intro b
  apply continuous_finsetSum
  intro a _
  by_cases h : f a = b
  · simp only [ite_eq_left h]
    exact continuous_apply a
  · simp only [ite_eq_right h]
    exact continuous_const

omit [Fintype β] in
lemma coarseVector_vectorOfPMF (f : α → β) (p : PMF α) :
    coarseVector f (vectorOfPMF p) = vectorOfPMF (p.map f) := by
  funext b
  unfold coarseVector vectorOfPMF
  rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro a _
    by_cases h : f a = b
    · simp [h]
    · simp only [ite_eq_right h, ite_eq_right (Ne.symm h), ENNReal.toReal_zero]
  · intro a _
    split_ifs <;> simp [p.apply_ne_top]

lemma entropyVector_vectorOfPMF (p : PMF α) :
    entropyVector (vectorOfPMF p) = finiteEntropy p (Set.toFinite _) := by
  symm
  exact finiteEntropy_eq_sum_of_support_subset p (Set.toFinite _) Finset.univ (by simp)

/-- The ordinary entropy of a fine label conditioned on its coarse statistic. -/
def conditionalVector (f : α → β) (x : α → ℝ) : ℝ :=
  entropyVector x - entropyVector (coarseVector f x)

@[fun_prop] lemma continuous_conditionalVector (f : α → β) : Continuous (conditionalVector f) := by
  unfold conditionalVector
  fun_prop

lemma conditionalVector_vectorOfPMF (f : α → β) (p : PMF α) :
    conditionalVector f (vectorOfPMF p) = conditionalEntropy p (Set.toFinite _) f := by
  rw [conditionalVector, coarseVector_vectorOfPMF, entropyVector_vectorOfPMF,
    entropyVector_vectorOfPMF, conditionalEntropy_eq_entropy_sub]

end ExactOverlaps.ProbabilityVectors
