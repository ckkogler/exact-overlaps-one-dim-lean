module

public import ExactOverlaps.Entropy.StatisticFactors
public import ExactOverlaps.Entropy.ConditionalIncrement
public import ExactOverlaps.Probability.CutObservations
public import ExactOverlaps.Probability.PoissonGenerator

/-!
# Exact entropy derivative of finite Poisson observations

Activating one cut adds its side statistic to the previously observed cut
label. The two descriptions recover one another exactly. The finite Poisson
generator and conditional chain rule therefore identify the true entropy
derivative, with the old cut labels included in the conditioning.
-/

@[expose] public section

open scoped BigOperators Classical
open ExactOverlaps.Poisson

namespace ExactOverlaps.Entropy

lemma cutLabel_update_true {ι α : Type*} (side : ι → α → Bool)
    (c : ι → Bool) (i : ι) (a : α) :
    cutLabel side (Function.update c i true) a =
      Function.update (cutLabel side c a) i (side i a) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [cutLabel]
  · simp [cutLabel, Function.update_of_ne hj]

lemma cutLabel_update_recover {ι α : Type*} (side : ι → α → Bool)
    (c : ι → Bool) (i : ι) (hc : c i = false) (a : α) :
    Function.update (cutLabel side (Function.update c i true) a) i false = cutLabel side c a := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [cutLabel, hc]
  · simp [cutLabel, Function.update_of_ne hj]

lemma conditional_cutLabel_update_eq_pair {ι α β : Type*} (p : PMF α)
    (hp : p.support.Finite) (s : α → β) (side : ι → α → Bool)
    (c : ι → Bool) (i : ι) (hc : c i = false) :
    averageStatisticConditionalEntropy p hp s (cutLabel side (Function.update c i true)) =
      averageStatisticConditionalEntropy p hp s (fun a ↦ (cutLabel side c a, side i a)) := by
  apply averageStatisticConditionalEntropy_eq_of_mutual_factors p hp s
    (cutLabel side (Function.update c i true)) (fun a ↦ (cutLabel side c a, side i a))
    (fun z ↦ (Function.update z i false, z i)) (fun z ↦ Function.update z.1 i z.2)
  · intro a _
    apply Prod.ext
    · exact (cutLabel_update_recover side c i hc a).symm
    · simp [cutLabel]
  · intro a _
    exact cutLabel_update_true side c i a

theorem conditional_cutLabel_increment {ι α β : Type*} (p : PMF α)
    (hp : p.support.Finite) (s : α → β) (side : ι → α → Bool)
    (c : ι → Bool) (i : ι) (hc : c i = false) :
    averageStatisticConditionalEntropy p hp s (cutLabel side (Function.update c i true)) -
        averageStatisticConditionalEntropy p hp s (cutLabel side c) =
      averageStatisticConditionalEntropy p hp (fun a ↦ (s a, cutLabel side c a)) (side i) := by
  rw [conditional_cutLabel_update_eq_pair p hp s side c i hc]
  exact averageStatisticConditionalEntropy_increment p hp s (cutLabel side c) (side i)

noncomputable def revealedEntropy {ι α β : Type*} [Fintype ι] (p : PMF α)
    (hp : p.support.Finite) (s : α → β) (side : ι → α → Bool) (d : ι → ℝ) (t : ℝ) : ℝ :=
  cutAverage d (fun c ↦ averageStatisticConditionalEntropy p hp s (cutLabel side c)) t

theorem hasDerivAt_revealedEntropy {ι α β : Type*} [Fintype ι] (p : PMF α)
    (hp : p.support.Finite) (s : α → β) (side : ι → α → Bool) (d : ι → ℝ) (t : ℝ) :
    HasDerivAt (revealedEntropy p hp s side d)
      (∑ c : ι → Bool, cutWeight d t c * ∑ i, if c i then 0 else d i *
        averageStatisticConditionalEntropy p hp (fun a ↦ (s a, cutLabel side c a)) (side i)) t := by
  unfold revealedEntropy
  have h := hasDerivAt_cutAverage d
    (fun c ↦ averageStatisticConditionalEntropy p hp s (cutLabel side c)) t
  convert h using 1
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  cases hc : c i
  · simp only [Bool.false_eq_true, ite_false]
    rw [conditional_cutLabel_increment p hp s side c i hc]
  · simp

end ExactOverlaps.Entropy
