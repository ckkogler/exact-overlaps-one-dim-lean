/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.GaussianScaleEntropy.Basic
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.Algebra.InfiniteSum.Group

/-!
# Uniform continuity of countable entropy under a common summable envelope

A finite core uses uniform continuity of negative p log p on the unit
interval. Both complementary tails are controlled by the same summable
sequence. This quantitative interface does not assume finite support.
-/

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology

namespace ExactOverlaps.GaussianScaleEntropy

lemma exists_finite_entropy_core {G : ℤ → ℝ} (hG : Summable G)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset ℤ, (∑' k : ℤ, G k) - ∑ k ∈ S, G k < ε := by
  have h := (tendsto_order.mp hG.hasSum).1
    ((∑' k : ℤ, G k) - ε) (by linarith)
  obtain ⟨S, hS⟩ := h.exists
  exact ⟨S, by linarith⟩

lemma entropy_tsum_sub_sum_le {f G : ℤ → ℝ} (hf0 : ∀ k, 0 ≤ f k)
    (hfG : ∀ k, f k ≤ G k) (hG : Summable G) (S : Finset ℤ) :
    (∑' k, f k) - ∑ k ∈ S, f k ≤ (∑' k, G k) - ∑ k ∈ S, G k := by
  have hf := Summable.of_nonneg_of_le hf0 hfG hG
  have htail := Summable.tsum_le_tsum (fun k : ↑((S : Set ℤ)ᶜ) ↦ hfG k)
    (hf.subtype _) (hG.subtype _)
  have hfe := hf.sum_add_tsum_compl (s := S)
  have hGe := hG.sum_add_tsum_compl (s := S)
  linarith

lemma uniform_negMulLog_tsum {G : ℤ → ℝ} (hG : Summable G)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ p q : ℤ → ℝ,
      (∀ k, p k ∈ Icc (0 : ℝ) 1) → (∀ k, q k ∈ Icc (0 : ℝ) 1) →
      (∀ k, Real.negMulLog (p k) ≤ G k) → (∀ k, Real.negMulLog (q k) ≤ G k) →
      (∀ k, |p k - q k| < δ) →
      |(∑' k, Real.negMulLog (p k)) - ∑' k, Real.negMulLog (q k)| < ε := by
  classical
  obtain ⟨S, hS⟩ := exists_finite_entropy_core hG (show 0 < ε / 4 by positivity)
  let η := ε / (2 * ((S.card : ℝ) + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous
    (Real.continuous_negMulLog.continuousOn (s := Icc (0 : ℝ) 1))
  obtain ⟨δ, hδ, hu⟩ := Metric.uniformContinuousOn_iff.mp huc η hη
  refine ⟨δ, hδ, ?_⟩
  intro p q hp hq hpG hqG hpq
  let f := fun k ↦ Real.negMulLog (p k)
  let g := fun k ↦ Real.negMulLog (q k)
  have hf0 : ∀ k, 0 ≤ f k := fun k ↦ Real.negMulLog_nonneg (hp k).1 (hp k).2
  have hg0 : ∀ k, 0 ≤ g k := fun k ↦ Real.negMulLog_nonneg (hq k).1 (hq k).2
  have hf := Summable.of_nonneg_of_le hf0 hpG hG
  have hg := Summable.of_nonneg_of_le hg0 hqG hG
  have hfd := entropy_tsum_sub_sum_le hf0 hpG hG S
  have hgd := entropy_tsum_sub_sum_le hg0 hqG hG S
  have hfn : 0 ≤ (∑' k, f k) - ∑ k ∈ S, f k := by
    rw [sub_nonneg]
    exact hf.sum_le_tsum S (fun k _ ↦ hf0 k)
  have hgn : 0 ≤ (∑' k, g k) - ∑ k ∈ S, g k := by
    rw [sub_nonneg]
    exact hg.sum_le_tsum S (fun k _ ↦ hg0 k)
  have hcore : |(∑ k ∈ S, f k) - ∑ k ∈ S, g k| ≤ (S.card : ℝ) * η := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ k ∈ S, |f k - g k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ S, η := Finset.sum_le_sum (fun k _ ↦ by
        exact (hu (p k) (hp k) (q k) (hq k) (by simpa only [Real.dist_eq] using hpq k)).le)
      _ = _ := by simp
  have hηbound : (S.card : ℝ) * η < ε / 2 := by
    dsimp [η]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * ((S.card : ℝ) + 1))).mpr
    nlinarith
  have htotal : |(∑' k, f k) - ∑' k, g k| ≤
      |(∑ k ∈ S, f k) - ∑ k ∈ S, g k| +
        ((∑' k, f k) - ∑ k ∈ S, f k) + ((∑' k, g k) - ∑ k ∈ S, g k) := by
    apply abs_le.mpr
    constructor <;> linarith [neg_abs_le ((∑ k ∈ S, f k) - ∑ k ∈ S, g k),
      le_abs_self ((∑ k ∈ S, f k) - ∑ k ∈ S, g k)]
  change |(∑' k, f k) - ∑' k, g k| < ε
  linarith

end ExactOverlaps.GaussianScaleEntropy
