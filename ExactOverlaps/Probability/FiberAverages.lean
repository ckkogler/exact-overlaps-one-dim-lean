module

public import ExactOverlaps.Probability.IndexedQuantile
public import ExactOverlaps.Probability.ConditionalRefinement

/-!
# Averaging functionals of actual conditional finite laws

A conditional functional is zero on null observation labels and evaluates
the genuine normalized law on positive labels. Averaging over input atoms
is exactly averaging over positive observation labels with their marginal
probabilities. The functional may depend on its finite-support witness.
-/

@[expose] public section

open scoped BigOperators Classical
open ExactOverlaps.Entropy

namespace ExactOverlaps.FiniteProbability

noncomputable def fiberFunctional {α β : Type*} (p : PMF α) (hp : p.support.Finite)
    (f : α → β) (F : (q : PMF α) → q.support.Finite → ℝ) (b : β) : ℝ :=
  if hb : b ∈ (p.map f).support then
    F (conditionalPMF p f ⟨b, hb⟩) (conditionalPMF_support_finite p hp f ⟨b, hb⟩)
  else 0

noncomputable def meanFiberFunctional {α β : Type*} (p : PMF α) (hp : p.support.Finite)
    (f : α → β) (F : (q : PMF α) → q.support.Finite → ℝ) : ℝ :=
  expectation p hp (fun a ↦ fiberFunctional p hp f F (f a))

lemma finiteFunctional_congr {α : Type*} (F : (q : PMF α) → q.support.Finite → ℝ)
    {p q : PMF α} (he : p = q) (hp : p.support.Finite) (hq : q.support.Finite) :
    F p hp = F q hq := by
  cases he
  rfl

lemma fiberFunctional_positive {α β : Type*} (p : PMF α) (hp : p.support.Finite)
    (f : α → β) (F : (q : PMF α) → q.support.Finite → ℝ) (b : (p.map f).support) :
    fiberFunctional p hp f F b =
      F (conditionalPMF p f b) (conditionalPMF_support_finite p hp f b) := by
  unfold fiberFunctional
  rw [dite_eq_left b.property]

lemma fiberFunctional_at {α β : Type*} (p : PMF α) (hp : p.support.Finite)
    (f : α → β) (F : (q : PMF α) → q.support.Finite → ℝ) (a : p.support) :
    fiberFunctional p hp f F (f a) = F (conditionalAt p f a)
      (conditionalPMF_support_finite p hp f _) := by
  exact fiberFunctional_positive p hp f F
    ⟨f a, (PMF.mem_support_map_iff f p _).mpr ⟨a, a.property, rfl⟩⟩

theorem meanFiberFunctional_eq_sum {α β : Type*} (p : PMF α) (hp : p.support.Finite)
    (f : α → β) (F : (q : PMF α) → q.support.Finite → ℝ) :
    meanFiberFunctional p hp f F =
    (letI : Fintype (p.map f).support :=
      (show (p.map f).support.Finite from by simpa using hp.image f).fintype
    ∑ b : (p.map f).support, ((p.map f) b).toReal *
      F (conditionalPMF p f b) (conditionalPMF_support_finite p hp f b)) := by
  let hf : (p.map f).support.Finite := by simpa using hp.image f
  let : Fintype (p.map f).support := hf.fintype
  unfold meanFiberFunctional
  rw [← expectation_map p hp f (fiberFunctional p hp f F)]
  unfold expectation
  rw [Finset.sum_subtype hf.toFinset (by simp : ∀ b, b ∈ hf.toFinset ↔ b ∈ (p.map f).support)]
  apply Finset.sum_congr rfl
  intro b _
  rw [fiberFunctional_positive]

lemma meanFiberFunctional_mono {α β : Type*} (p : PMF α) (hp : p.support.Finite)
    (f : α → β) (F G : (q : PMF α) → q.support.Finite → ℝ)
    (h : ∀ b : (p.map f).support,
      F (conditionalPMF p f b) (conditionalPMF_support_finite p hp f b) ≤
      G (conditionalPMF p f b) (conditionalPMF_support_finite p hp f b)) :
    meanFiberFunctional p hp f F ≤ meanFiberFunctional p hp f G := by
  rw [meanFiberFunctional_eq_sum, meanFiberFunctional_eq_sum]
  exact Finset.sum_le_sum (fun b _ ↦ mul_le_mul_of_nonneg_left (h b) ENNReal.toReal_nonneg)

lemma meanFiberFunctional_const_mul {α β : Type*} (p : PMF α) (hp : p.support.Finite)
    (f : α → β) (F : (q : PMF α) → q.support.Finite → ℝ) (c : ℝ) :
    meanFiberFunctional p hp f (fun q hq ↦ c * F q hq) = c * meanFiberFunctional p hp f F := by
  rw [meanFiberFunctional_eq_sum, meanFiberFunctional_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

lemma meanFiberFunctional_sum {α β ι : Type*} [Fintype ι] (p : PMF α) (hp : p.support.Finite)
    (f : α → β) (F : ι → (q : PMF α) → q.support.Finite → ℝ) :
    meanFiberFunctional p hp f (fun q hq ↦ ∑ i, F i q hq) =
      ∑ i, meanFiberFunctional p hp f (F i) := by
  simp_rw [meanFiberFunctional_eq_sum, Finset.mul_sum]
  exact Finset.sum_comm

end ExactOverlaps.FiniteProbability
