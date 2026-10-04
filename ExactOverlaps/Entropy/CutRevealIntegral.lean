module

public import ExactOverlaps.Entropy.CutRevealEndpoints
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Integrating the true finite entropy reveal rate

The reveal rate is nonnegative for positive gap lengths and nonnegative
times. Its actual finite terminal entropy implies integrability by the
fundamental theorem of calculus on the positive half-line.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators Classical
open ExactOverlaps.Poisson

namespace ExactOverlaps.Entropy

noncomputable def revealedEntropyRate {ι α β : Type*} [Fintype ι] (p : PMF α)
    (hp : p.support.Finite) (s : α → β) (side : ι → α → Bool) (d : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ c : ι → Bool, cutWeight d t c * ∑ i, if c i then 0 else d i *
    averageStatisticConditionalEntropy p hp (fun a ↦ (s a, cutLabel side c a)) (side i)

lemma revealedEntropyRate_nonneg {ι α β : Type*} [Fintype ι] (p : PMF α)
    (hp : p.support.Finite) (s : α → β) (side : ι → α → Bool) (d : ι → ℝ)
    (hd : ∀ i, 0 ≤ d i) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ revealedEntropyRate p hp s side d t := by
  apply Finset.sum_nonneg
  intro c _
  apply mul_nonneg (cutWeight_nonneg d hd ht c)
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact le_rfl
  · apply mul_nonneg (hd i)
    unfold averageStatisticConditionalEntropy
    exact Finset.sum_nonneg (fun _ _ ↦ mul_nonneg ENNReal.toReal_nonneg
      (finiteEntropy_nonneg _ _))

theorem integrableOn_revealedEntropyRate {ι α β : Type*} [Fintype ι] (p : PMF α)
    (hp : p.support.Finite) (s : α → β) (side : ι → α → Bool) (d : ι → ℝ)
    (hd : ∀ i, 0 < d i) (hsep : Set.InjOn (fun a i ↦ side i a) p.support) :
    IntegrableOn (revealedEntropyRate p hp s side d) (Ioi 0) := by
  exact integrableOn_Ioi_deriv_of_nonneg'
    (fun t _ ↦ hasDerivAt_revealedEntropy p hp s side d t)
    (fun t ht ↦ revealedEntropyRate_nonneg p hp s side d (fun i ↦ (hd i).le) ht.le)
    (tendsto_revealedEntropy p hp s side d hd hsep)

theorem integral_revealedEntropyRate {ι α β : Type*} [Fintype ι] (p : PMF α)
    (hp : p.support.Finite) (s : α → β) (side : ι → α → Bool) (d : ι → ℝ)
    (hd : ∀ i, 0 < d i) (hsep : Set.InjOn (fun a i ↦ side i a) p.support) :
    (∫ t : ℝ in Ioi 0, revealedEntropyRate p hp s side d t) =
      finiteEntropy p hp - finiteEntropy (p.map s) (by simpa using hp.image s) := by
  unfold revealedEntropyRate
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun t (_ : t ∈ Ici (0 : ℝ)) ↦ hasDerivAt_revealedEntropy p hp s side d t)
    (fun t (ht : t ∈ Ioi (0 : ℝ)) ↦
      revealedEntropyRate_nonneg p hp s side d (fun i ↦ (hd i).le) ht.le)
    (tendsto_revealedEntropy p hp s side d hd hsep)
  simpa only [revealedEntropy_zero, sub_zero] using h

end ExactOverlaps.Entropy
