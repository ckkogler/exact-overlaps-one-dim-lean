module

public import ExactOverlaps.Probability.CDFEstimate

/-!
# Reflected cumulative estimates outside the finite endpoint exceptions

Reflection exchanges strict and weak cut inequalities. Almost every shift
avoids all differences of support atoms, which proves the reflected estimate
with its required almost-everywhere qualification.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators Classical

namespace ExactOverlaps.FiniteProbability

lemma expectation_congr {α : Type*} (p : PMF α) (hp : p.support.Finite)
    {f g : α → ℝ} (h : ∀ a ∈ p.support, f a = g a) :
    expectation p hp f = expectation p hp g := by
  unfold expectation
  apply Finset.sum_congr rfl
  intro a ha
  rw [h a (by simpa using ha)]

lemma one_sub_cumulativeMass_eq_reflected {α : Type*} (p : PMF α)
    (hp : p.support.Finite) (x : α → ℝ) (a : ℝ)
    (hno : ∀ z ∈ p.support, x z ≠ a) :
    1 - cumulativeMass p hp x a = cumulativeMass p hp (fun z ↦ -x z) (-a) := by
  rw [one_sub_cumulativeMass]
  apply expectation_congr p hp
  intro z hz
  have hn := hno z hz
  change (if a < x z then (1 : ℝ) else 0) = if -x z ≤ -a then 1 else 0
  have he : a < x z ↔ -x z ≤ -a := by
    constructor
    · intro h
      linarith
    · intro h
      exact lt_of_le_of_ne (by linarith) (Ne.symm hn)
  simp only [he]

lemma ae_shift_not_support_atom {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (x : α → ℝ) :
    ∀ᵐ u : ℝ, ∀ a ∈ p.support, ∀ b ∈ p.support, x b ≠ x a - u := by
  apply (ae_ball_iff hp.countable).mpr
  intro a _
  apply (ae_ball_iff hp.countable).mpr
  intro b _
  filter_upwards [(Set.countable_singleton (x a - x b)).ae_notMem volume] with u hu
  have hn : u ≠ x a - x b := by simpa using hu
  intro he
  apply hn
  linarith

lemma distanceTail_neg {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (x : α → ℝ) (u : ℝ) : distanceTail p hp (fun a ↦ -x a) u = distanceTail p hp x u := by
  unfold distanceTail expectation
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have he : -x b + u < -x a ↔ x a + u < x b := by constructor <;> intro h <;> linarith
  simp only [he]
  ring

theorem ae_reflected_cdf_sqrt_odds_le {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (x : α → ℝ) :
    ∀ᵐ u : ℝ ∂volume.restrict (Ioi 0),
      expectation p hp (fun a ↦ Real.sqrt
        (cumulativeMass p hp x (x a - u) / (1 - cumulativeMass p hp x (x a - u)))) ≤
        3 * Real.sqrt (2 * distanceTail p hp x u) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi,
    ae_restrict_le (ae_shift_not_support_atom p hp x)] with u hu hno
  have h := cdf_sqrt_odds_le_statistic p hp (fun a ↦ -x a) hu.le
  rw [distanceTail_neg] at h
  have he : cdfOddsExpectation p hp (fun a ↦ -x a) u =
      expectation p hp (fun a ↦ Real.sqrt
        (cumulativeMass p hp x (x a - u) / (1 - cumulativeMass p hp x (x a - u)))) := by
    apply expectation_congr p hp
    intro a ha
    have hc := one_sub_cumulativeMass_eq_reflected p hp x (x a - u) (hno a ha)
    have harg : -(x a - u) = -x a + u := by ring
    rw [harg] at hc
    change Real.sqrt ((1 - cumulativeMass p hp (fun a ↦ -x a) (-x a + u)) /
      cumulativeMass p hp (fun a ↦ -x a) (-x a + u)) = _
    rw [← hc]
    congr 1
    ring
  rw [he] at h
  exact h

end ExactOverlaps.FiniteProbability
