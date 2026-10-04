/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.PrefixRatios
public import ExactOverlaps.StoppedConcatenation.StoppingRules
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! The first absolute-ratio crossing is an actual bounded stopping time. -/

@[expose] public section

open MeasureTheory
open scoped Classical

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι]

noncomputable def ratioCrossingTime (S : System ι) (r : ℝ) (hr : 0 < r) (ω : ℕ → ι) : ℕ :=
  Nat.find ((S.exists_uniform_ratio_crossing hr).imp (fun _ h ↦ h ω))

theorem ratioCrossingTime_upper (S : System ι) (r : ℝ) (hr : 0 < r) (ω : ℕ → ι) :
    |S.prefixRatio (S.ratioCrossingTime r hr ω) ω| ≤ r := by
  unfold ratioCrossingTime
  exact Nat.find_spec ((S.exists_uniform_ratio_crossing hr).imp (fun _ h ↦ h ω))

theorem ratioCrossingTime_le_iff (S : System ι) (r : ℝ) (hr : 0 < r) (ω : ℕ → ι) (n : ℕ) :
    S.ratioCrossingTime r hr ω ≤ n ↔ |S.prefixRatio n ω| ≤ r := by
  constructor
  · intro h
    exact (S.abs_prefixRatio_antitone ω h).trans (S.ratioCrossingTime_upper r hr ω)
  · intro h
    exact Nat.find_min' _ h

theorem before_ratioCrossingTime (S : System ι) (r : ℝ) (hr : 0 < r) (ω : ℕ → ι)
    {n : ℕ} (hn : n < S.ratioCrossingTime r hr ω) : r < |S.prefixRatio n ω| := by
  exact lt_of_not_ge (Nat.find_min _ hn)

theorem ratioCrossingTime_lower (S : System ι) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (hmin : ∀ i, a ≤ |(S.map i).ratio|)
    (ω : ℕ → ι) : a * r < |S.prefixRatio (S.ratioCrossingTime r hr ω) ω| := by
  cases ht : S.ratioCrossingTime r hr ω with
  | zero =>
    simp only [prefixRatio, Finset.range_zero, Finset.prod_empty, abs_one]
    exact lt_of_le_of_lt (mul_le_of_le_one_right ha.le hr1) ha1
  | succ n =>
    have hprev : r < |S.prefixRatio n ω| :=
      S.before_ratioCrossingTime r hr ω (by omega)
    rw [S.prefixRatio_succ, abs_mul]
    calc
      a * r < a * |S.prefixRatio n ω| := mul_lt_mul_of_pos_left hprev ha
      _ ≤ |S.prefixRatio n ω| * |(S.map (ω n)).ratio| := by
        rw [mul_comm a]
        exact mul_le_mul_of_nonneg_left (hmin _) (abs_nonneg _)

theorem ratioCrossingTime_antitone (S : System ι) {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hrs : r ≤ s) (ω : ℕ → ι) : S.ratioCrossingTime s hs ω ≤ S.ratioCrossingTime r hr ω :=
  (S.ratioCrossingTime_le_iff s hs ω _).2 ((S.ratioCrossingTime_upper r hr ω).trans hrs)

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

noncomputable def ratioCrossingRule (S : System ι) (r : ℝ) (hr : 0 < r) :
    StoppedConcatenation.BoundedStoppingRule ι where
  time := S.ratioCrossingTime r hr
  horizon := (S.exists_uniform_ratio_crossing hr).choose
  bounded := fun ω ↦ (S.ratioCrossingTime_le_iff r hr ω _).2
    ((S.exists_uniform_ratio_crossing hr).choose_spec ω)
  adapted := by
    intro n
    change MeasurableSet[StoppedConcatenation.incrementFiltration (ι := ι) n]
      {ω | (S.ratioCrossingTime r hr ω : WithTop ℕ) ≤ (n : WithTop ℕ)}
    have he : {ω | (S.ratioCrossingTime r hr ω : WithTop ℕ) ≤ n} =
        {ω | |S.prefixRatio n ω| ≤ r} := by
      ext ω
      change (S.ratioCrossingTime r hr ω : WithTop ℕ) ≤ n ↔ _
      simpa using S.ratioCrossingTime_le_iff r hr ω n
    rw [he]
    exact measurableSet_le
      (continuous_abs.measurable.comp (S.measurable_prefixRatio_at n)) measurable_const

end ExactOverlaps.SelfSimilar.System
