module

public import ExactOverlaps.Entropy.BinaryPrediction
public import ExactOverlaps.Entropy.ProductPredictor
public import ExactOverlaps.Probability.IndependentExpectations
public import ExactOverlaps.Probability.CDFAtoms

/-!
# The actual predictor for a cut given an independent sum

The two marginal cumulative masses define a supported predictor for the
event that the first input lies below a cut. The only excluded cut locations
are atoms of the first real statistic, as required by the strict endpoint
argument in the cumulative-entropy proof.
-/

@[expose] public section

open scoped Classical
open ExactOverlaps.FiniteProbability

namespace ExactOverlaps.Entropy

noncomputable def sumCutPredictor {α β : Type*} (p : PMF α) (q : PMF β)
    (hp : p.support.Finite) (hq : q.support.Finite) (x : α → ℝ) (y : β → ℝ)
    (a s : ℝ) : ℝ := productPredictor (cumulativeMass p hp x a) (cumulativeMass q hq y (s - a))

lemma sumCutPredictor_mem_Icc {α β : Type*} (p : PMF α) (q : PMF β)
    (hp : p.support.Finite) (hq : q.support.Finite) (x : α → ℝ) (y : β → ℝ)
    (a s : ℝ) : sumCutPredictor p q hp hq x y a s ∈ Set.Icc 0 1 := by
  exact productPredictor_mem_Icc
    ⟨cumulativeMass_nonneg p hp x a, cumulativeMass_le_one p hp x a⟩
    ⟨cumulativeMass_nonneg q hq y (s - a), cumulativeMass_le_one q hq y (s - a)⟩

lemma sumCutPredictor_pos_of_lt {α β : Type*} (p : PMF α) (q : PMF β)
    (hp : p.support.Finite) (hq : q.support.Finite) (x : α → ℝ) (y : β → ℝ)
    (u : α) (v : β) (hu : u ∈ p.support) (hv : v ∈ q.support) {a : ℝ} (hua : x u < a) :
    0 < sumCutPredictor p q hp hq x y a (x u + y v) := by
  apply productPredictor_pos (cumulativeMass_pos_of_atom_le p hp x u hu hua.le)
    (cumulativeMass_lt_one_of_lt_atom q hq y v hv (by linarith))
  exact mul_nonneg (sub_nonneg.mpr (cumulativeMass_le_one p hp x a))
    (cumulativeMass_nonneg q hq y _)

lemma sumCutPredictor_lt_one_of_lt {α β : Type*} (p : PMF α) (q : PMF β)
    (hp : p.support.Finite) (hq : q.support.Finite) (x : α → ℝ) (y : β → ℝ)
    (u : α) (v : β) (hu : u ∈ p.support) (hv : v ∈ q.support) {a : ℝ} (hau : a < x u) :
    sumCutPredictor p q hp hq x y a (x u + y v) < 1 := by
  apply productPredictor_lt_one (cumulativeMass_lt_one_of_lt_atom p hp x u hu hau)
    (cumulativeMass_pos_of_atom_le q hq y v hv (by linarith))
  exact mul_nonneg (cumulativeMass_nonneg p hp x a)
    (sub_nonneg.mpr (cumulativeMass_le_one q hq y _))

theorem conditional_sum_cut_entropy_le_loss {α β : Type*} (p : PMF α) (q : PMF β)
    (hp : p.support.Finite) (hq : q.support.Finite) (x : α → ℝ) (y : β → ℝ)
    (a : ℝ) (ha : ∀ u ∈ p.support, x u ≠ a) :
    averageStatisticConditionalEntropy (independentPair p q) (independentPair_support_finite p q hp hq)
      (fun z ↦ x z.1 + y z.2) (fun z ↦ decide (x z.1 ≤ a)) ≤
      expectation (independentPair p q) (independentPair_support_finite p q hp hq)
        (fun z ↦ if x z.1 ≤ a then -Real.log (sumCutPredictor p q hp hq x y a (x z.1 + y z.2))
          else -Real.log (1 - sumCutPredictor p q hp hq x y a (x z.1 + y z.2))) := by
  have h := averageStatisticConditionalEntropy_bool_le_prediction (independentPair p q)
    (independentPair_support_finite p q hp hq) (fun z ↦ x z.1 + y z.2)
    (fun z ↦ decide (x z.1 ≤ a)) (sumCutPredictor p q hp hq x y a)
    (fun s _ ↦ sumCutPredictor_mem_Icc p q hp hq x y a s)
    (fun z hz hside ↦ by
      rw [independentPair_support] at hz
      have hxa : x z.1 ≤ a := by simpa using hside
      exact (sumCutPredictor_pos_of_lt p q hp hq x y z.1 z.2 hz.1 hz.2
        (lt_of_le_of_ne hxa (ha z.1 hz.1))).ne')
    (fun z hz hside ↦ by
      rw [independentPair_support] at hz
      have hax : a < x z.1 := by simpa using hside
      exact (sumCutPredictor_lt_one_of_lt p q hp hq x y z.1 z.2 hz.1 hz.2 hax).ne)
  simpa using h

end ExactOverlaps.Entropy
