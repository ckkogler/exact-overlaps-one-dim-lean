module

public import ExactOverlaps.Entropy.CrossEntropy
public import ExactOverlaps.Entropy.Submodularity
public import ExactOverlaps.Probability.IndexedQuantile
public import ExactOverlaps.Probability.ConditionalVarianceTower

/-!
# Logarithmic prediction bounds for actual binary conditional entropy

A predictor must assign nonzero probability to each event that occurs with
positive probability. Under that support condition its expected logarithmic
loss bounds the genuine entropy, both before and after an observation.
-/

@[expose] public section

open scoped BigOperators ENNReal Classical

namespace ExactOverlaps.Entropy

theorem finiteEntropy_map_bool_le_prediction {α : Type*} (p : PMF α)
    (hp : p.support.Finite) (g : α → Bool) {q : ℝ} (hq : q ∈ Set.Icc 0 1)
    (htrue : ∀ a ∈ p.support, g a = true → q ≠ 0)
    (hfalse : ∀ a ∈ p.support, g a = false → q ≠ 1) :
    finiteEntropy (p.map g) (by simpa using hp.image g) ≤
      FiniteProbability.expectation p hp
        (fun a ↦ if g a then -Real.log q else -Real.log (1 - q)) := by
  let hg : (p.map g).support.Finite := by simpa using hp.image g
  have hmass : (∑ b : Bool, ((p.map g) b).toReal) = 1 := sum_pmf_toReal _
  have hpred : (∑ b : Bool, if b then q else 1 - q) ≤ 1 := by
    simp only [Fintype.sum_bool]
    change q + (1 - q) ≤ 1
    linarith
  have h := finite_entropy_le_crossEntropy Finset.univ
    (fun b : Bool ↦ ((p.map g) b).toReal) (fun b : Bool ↦ if b then q else 1 - q)
    (fun _ _ ↦ ENNReal.toReal_nonneg)
    (fun b _ ↦ by cases b <;> simp [hq.1, sub_nonneg.mpr hq.2]) hmass hpred
    (fun b _ hb ↦ by
      have hbmem : b ∈ (p.map g).support := by
        rw [PMF.mem_support_iff]
        intro hz
        exact hb (by simp [hz])
      obtain ⟨a, ha, hga⟩ := (PMF.mem_support_map_iff g p b).mp hbmem
      cases b
      · change 1 - q ≠ 0
        exact sub_ne_zero.mpr (Ne.symm (hfalse a ha hga))
      · exact htrue a ha hga)
  rw [finiteEntropy_eq_sum_of_support_subset (p.map g) hg Finset.univ
    (fun _ _ ↦ Finset.mem_univ _)]
  apply le_trans h
  apply le_of_eq
  rw [← FiniteProbability.expectation_eq_sum_univ (p.map g) hg,
    FiniteProbability.expectation_map p hp g]
  congr 1
  funext a
  cases g a <;> simp

theorem averageStatisticConditionalEntropy_bool_le_prediction {α β : Type*}
    (p : PMF α) (hp : p.support.Finite) (f : α → β) (g : α → Bool) (q : β → ℝ)
    (hq : ∀ b ∈ (p.map f).support, q b ∈ Set.Icc 0 1)
    (htrue : ∀ a ∈ p.support, g a = true → q (f a) ≠ 0)
    (hfalse : ∀ a ∈ p.support, g a = false → q (f a) ≠ 1) :
    averageStatisticConditionalEntropy p hp f g ≤
      FiniteProbability.expectation p hp
        (fun a ↦ if g a then -Real.log (q (f a)) else -Real.log (1 - q (f a))) := by
  let hf : (p.map f).support.Finite := by simpa using hp.image f
  let : Fintype (p.map f).support := hf.fintype
  let v (a : α) := if g a then -Real.log (q (f a)) else -Real.log (1 - q (f a))
  change averageStatisticConditionalEntropy p hp f g ≤ FiniteProbability.expectation p hp v
  rw [← FiniteProbability.sum_marginal_mul_expectation_conditional p hp f v]
  unfold averageStatisticConditionalEntropy
  apply Finset.sum_le_sum
  intro b _
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  have hb := finiteEntropy_map_bool_le_prediction (conditionalPMF p f b)
    (conditionalPMF_support_finite p hp f b) g (hq b b.property)
    (fun a ha hga ↦ by
      rw [conditionalPMF_support] at ha
      have hfa : f a = b.val := ha.1
      rw [← hfa]
      exact htrue a ha.2 hga)
    (fun a ha hga ↦ by
      rw [conditionalPMF_support] at ha
      have hfa : f a = b.val := ha.1
      rw [← hfa]
      exact hfalse a ha.2 hga)
  apply hb.trans_eq
  unfold FiniteProbability.expectation
  apply Finset.sum_congr rfl
  intro a ha
  have hs : a ∈ (conditionalPMF p f b).support := by simpa using ha
  rw [conditionalPMF_support] at hs
  have hfa : f a = b.val := hs.1
  simp only [v, hfa]

end ExactOverlaps.Entropy
