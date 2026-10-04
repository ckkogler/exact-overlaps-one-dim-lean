module

public import ExactOverlaps.SelfSimilar.WordBounds
public import ExactOverlaps.SelfSimilar.BernoulliBlocks
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
The real affine coding map is constructed as an absolutely convergent
series. Its convergence and uniform bounds use absolute contraction
ratios, while the series itself keeps every signed multiplier.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι]

noncomputable def prefixRatio (S : System ι) (n : ℕ) (ω : ℕ → ι) : ℝ :=
  ∏ j ∈ Finset.range n, (S.map (ω j)).ratio

noncomputable def codingTerm (S : System ι) (n : ℕ) (ω : ℕ → ι) : ℝ :=
  S.prefixRatio n ω * (S.map (ω n)).shift

/-- The limit point coded by an infinite sequence of branches. -/
noncomputable def coding (S : System ι) (ω : ℕ → ι) : ℝ :=
  ∑' n, S.codingTerm n ω

theorem prefixRatio_succ (S : System ι) (n : ℕ) (ω : ℕ → ι) :
    S.prefixRatio (n + 1) ω = S.prefixRatio n ω * (S.map (ω n)).ratio := by
  exact Finset.prod_range_succ _ _

theorem prefixRatio_succ_shift (S : System ι) (n : ℕ) (ω : ℕ → ι) :
    S.prefixRatio (n + 1) ω = (S.map (ω 0)).ratio * S.prefixRatio n (Bernoulli.shift ω) := by
  unfold prefixRatio
  rw [Finset.prod_range_succ']
  simp only [Bernoulli.shift]
  ring

theorem codingTerm_succ (S : System ι) (n : ℕ) (ω : ℕ → ι) :
    S.codingTerm (n + 1) ω = (S.map (ω 0)).ratio * S.codingTerm n (Bernoulli.shift ω) := by
  rw [codingTerm, prefixRatio_succ_shift, codingTerm]
  rw [mul_assoc]
  rfl

theorem abs_prefixRatio_le (S : System ι) {c : ℝ} (hc : 0 ≤ c)
    (hmax : ∀ i, |(S.map i).ratio| ≤ c) (n : ℕ) (ω : ℕ → ι) :
    |S.prefixRatio n ω| ≤ c ^ n := by
  induction n with
  | zero => simp [prefixRatio]
  | succ n ih =>
      rw [prefixRatio_succ, abs_mul, pow_succ]
      exact mul_le_mul ih (hmax _) (abs_nonneg _) (pow_nonneg hc n)

theorem abs_codingTerm_le (S : System ι) {c M : ℝ} (hc : 0 ≤ c)
    (hmax : ∀ i, |(S.map i).ratio| ≤ c) (hshift : ∀ i, |(S.map i).shift| ≤ M)
    (n : ℕ) (ω : ℕ → ι) : |S.codingTerm n ω| ≤ c ^ n * M := by
  rw [codingTerm, abs_mul]
  exact mul_le_mul (S.abs_prefixRatio_le hc hmax n ω) (hshift _)
    (abs_nonneg _) (pow_nonneg hc n)

theorem summable_codingTerm (S : System ι) (ω : ℕ → ι) :
    Summable (fun n ↦ S.codingTerm n ω) := by
  obtain ⟨c, M, hc, hc1, _, hmax, hshift⟩ := S.exists_uniform_bounds
  apply ((summable_geometric_of_lt_one hc.le hc1).mul_right M).of_norm_bounded
  intro n
  simpa only [Real.norm_eq_abs] using S.abs_codingTerm_le hc.le hmax hshift n ω

theorem abs_coding_le (S : System ι) {c M : ℝ} (hc : 0 ≤ c) (hc1 : c < 1)
    (hmax : ∀ i, |(S.map i).ratio| ≤ c) (hshift : ∀ i, |(S.map i).shift| ≤ M)
    (ω : ℕ → ι) : |S.coding ω| ≤ M / (1 - c) := by
  have hs : HasSum (fun n : ℕ ↦ c ^ n * M) ((1 - c)⁻¹ * M) :=
    (hasSum_geometric_of_lt_one hc hc1).mul_right M
  have h := tsum_of_norm_bounded (f := fun n ↦ S.codingTerm n ω) hs (fun n ↦ by
    simpa only [Real.norm_eq_abs] using S.abs_codingTerm_le hc hmax hshift n ω)
  simpa only [Real.norm_eq_abs, coding, div_eq_inv_mul] using h

/-- The coding satisfies the affine head-tail identity at every sequence. -/
theorem coding_shift (S : System ι) (ω : ℕ → ι) :
    S.coding ω = (S.map (ω 0)) (S.coding (Bernoulli.shift ω)) := by
  have htail : (∑' n, S.codingTerm (n + 1) ω) =
      (S.map (ω 0)).ratio * S.coding (Bernoulli.shift ω) := by
    calc
      _ = ∑' n, (S.map (ω 0)).ratio * S.codingTerm n (Bernoulli.shift ω) :=
        tsum_congr (fun n ↦ S.codingTerm_succ n ω)
      _ = _ := tsum_mul_left
  calc
    S.coding ω = S.codingTerm 0 ω + ∑' n, S.codingTerm (n + 1) ω :=
      (S.summable_codingTerm ω).tsum_eq_zero_add
    _ = _ := by
      rw [htail]
      simp only [codingTerm, prefixRatio, Finset.range_zero, Finset.prod_empty,
        one_mul]
      ring

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem measurable_codingTerm (S : System ι) (n : ℕ) : Measurable (S.codingTerm n) := by
  have hr : Measurable (fun i ↦ (S.map i).ratio) := measurable_of_finite _
  have hb : Measurable (fun i ↦ (S.map i).shift) := measurable_of_finite _
  unfold codingTerm prefixRatio
  exact (Finset.measurable_fun_prod _ (fun j _ ↦ hr.comp (measurable_pi_apply j))).mul
    (hb.comp (measurable_pi_apply n))

theorem measurable_coding (S : System ι) : Measurable S.coding := by
  exact Measurable.tsum (fun n ↦ S.measurable_codingTerm n)

end ExactOverlaps.SelfSimilar.System
