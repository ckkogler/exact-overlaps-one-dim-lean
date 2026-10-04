module

public import ExactOverlaps.Probability.FiniteMoments
public import ExactOverlaps.Entropy.CrossEntropy

/-!
# Splitting the square-root odds estimate at one half

The high part is controlled by Cauchy--Schwarz. The low part is bounded by
an inverse square root. A separate finite quantile estimate supplies the
low-part hypothesis in the final assembly lemma.
-/

@[expose] public section

open scoped BigOperators Classical

namespace ExactOverlaps.FiniteProbability

lemma sqrt_odds_sq_le_of_half_le {z : ℝ} (hz : z ≤ 1) (hl : 1 / 2 ≤ z) :
    (Real.sqrt ((1 - z) / z)) ^ 2 ≤ 2 * (1 - z) := by
  have hzpos : 0 < z := by linarith
  rw [Real.sq_sqrt (div_nonneg (sub_nonneg.mpr hz) hzpos.le)]
  apply (div_le_iff₀ hzpos).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hz) (show 0 ≤ 2 * z - 1 by linarith)]

lemma sqrt_odds_le_inv_sqrt {z : ℝ} (hz : z ∈ Set.Icc 0 1) :
    Real.sqrt ((1 - z) / z) ≤ 1 / Real.sqrt z := by
  rw [Real.sqrt_div (sub_nonneg.mpr hz.2)]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg z)
  apply (Real.sqrt_le_iff).mpr
  exact ⟨by norm_num, by nlinarith [hz.1]⟩

lemma below_half_mass_le_twice_complement {α : Type*} (p : PMF α)
    (hp : p.support.Finite) (z : α → ℝ) (hz : ∀ a ∈ p.support, z a ≤ 1) :
    expectation p hp (fun a ↦ if z a < 1 / 2 then 1 else 0) ≤
      2 * expectation p hp (fun a ↦ 1 - z a) := by
  rw [← expectation_const_mul]
  apply expectation_mono p hp
  intro a ha
  have hza := hz a ha
  split_ifs with hl <;> linarith

lemma expectation_high_sqrt_odds_le {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (z : α → ℝ) (hz : ∀ a ∈ p.support, z a ≤ 1) :
    expectation p hp (fun a ↦ if z a < 1 / 2 then 0 else Real.sqrt ((1 - z a) / z a)) ≤
      Real.sqrt (2 * expectation p hp (fun a ↦ 1 - z a)) := by
  let f (a : α) := if z a < 1 / 2 then 0 else Real.sqrt ((1 - z a) / z a)
  have hsq := expectation_sq_le_expectation_sq p hp f
  have hle : expectation p hp (fun a ↦ f a ^ 2) ≤
      2 * expectation p hp (fun a ↦ 1 - z a) := by
    rw [← expectation_const_mul]
    apply expectation_mono p hp
    intro a ha
    dsimp [f]
    split_ifs with hl
    · have hza := hz a ha
      nlinarith
    · exact sqrt_odds_sq_le_of_half_le (hz a ha) (le_of_not_gt hl)
  have hn : 0 ≤ 2 * expectation p hp (fun a ↦ 1 - z a) :=
    mul_nonneg (by norm_num) (expectation_nonneg p hp (fun a ha ↦ sub_nonneg.mpr (hz a ha)))
  change expectation p hp f ≤ _
  have hs := Real.sq_sqrt hn
  nlinarith [hsq.trans hle, Real.sqrt_nonneg (2 * expectation p hp (fun a ↦ 1 - z a))]

/-- Assembly of the preliminary estimate once the finite lower-tail quantile bound is supplied. -/
lemma expectation_sqrt_odds_le_of_lower_tail {α : Type*} (p : PMF α)
    (hp : p.support.Finite) (z : α → ℝ) (hz : ∀ a ∈ p.support, z a ∈ Set.Icc 0 1)
    (hlow : expectation p hp (fun a ↦ if z a < 1 / 2 then 1 / Real.sqrt (z a) else 0) ≤
      2 * Real.sqrt (expectation p hp (fun a ↦ if z a < 1 / 2 then 1 else 0))) :
    expectation p hp (fun a ↦ Real.sqrt ((1 - z a) / z a)) ≤
      3 * Real.sqrt (2 * expectation p hp (fun a ↦ 1 - z a)) := by
  have hsplit : expectation p hp (fun a ↦ Real.sqrt ((1 - z a) / z a)) =
      expectation p hp (fun a ↦ if z a < 1 / 2 then Real.sqrt ((1 - z a) / z a) else 0) +
      expectation p hp (fun a ↦ if z a < 1 / 2 then 0 else Real.sqrt ((1 - z a) / z a)) := by
    rw [← expectation_add]
    unfold expectation
    apply Finset.sum_congr rfl
    intro a _
    dsimp only
    split_ifs <;> simp
  have hl : expectation p hp (fun a ↦ if z a < 1 / 2 then Real.sqrt ((1 - z a) / z a) else 0) ≤
      2 * Real.sqrt (expectation p hp (fun a ↦ if z a < 1 / 2 then 1 else 0)) := by
    apply le_trans _ hlow
    apply expectation_mono p hp
    intro a ha
    split_ifs
    · exact sqrt_odds_le_inv_sqrt (hz a ha)
    · exact le_rfl
  have hh := expectation_high_sqrt_odds_le p hp z (fun a ha ↦ (hz a ha).2)
  have hq := Real.sqrt_le_sqrt (below_half_mass_le_twice_complement p hp z (fun a ha ↦ (hz a ha).2))
  rw [hsplit]
  linarith

end ExactOverlaps.FiniteProbability
