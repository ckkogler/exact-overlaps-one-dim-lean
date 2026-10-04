module

public import ExactOverlaps.Entropy.CutReveal
public import ExactOverlaps.Probability.PoissonEndpoints

/-!
# Entropy endpoints of complete finite cut observations

The initial observation is constant. When the full family of cuts separates
the actual support, the terminal entropy equals the original entropy minus
the entropy of the statistic retained in the conditioning.
-/

@[expose] public section

open Filter
open scoped Topology Classical
open ExactOverlaps.Poisson

namespace ExactOverlaps.Entropy

lemma averageStatisticConditionalEntropy_const {α β γ : Type*} (p : PMF α)
    (hp : p.support.Finite) (s : α → β) (c : γ) :
    averageStatisticConditionalEntropy p hp s (fun _ ↦ c) = 0 := by
  have h := statisticEntropy_chain_rule p hp s (fun _ ↦ c)
  have he := finiteEntropy_map_of_injective (p.map s)
    (show (p.map s).support.Finite from by simpa using hp.image s)
    (f := fun b : β ↦ (b, c)) (fun _ _ h ↦ (Prod.mk.inj h).1)
  simp only [PMF.map_comp, Function.comp_def] at he
  rw [he] at h
  linarith

lemma averageStatisticConditionalEntropy_eq_sub_of_injective {α β γ : Type*}
    (p : PMF α) (hp : p.support.Finite) (s : α → β) (g : α → γ)
    (hg : Set.InjOn g p.support) :
    averageStatisticConditionalEntropy p hp s g =
      finiteEntropy p hp - finiteEntropy (p.map s) (by simpa using hp.image s) := by
  have h := statisticEntropy_chain_rule p hp s g
  have he := finiteEntropy_map_of_injective_support p hp
    (f := fun a ↦ (s a, g a)) (fun _ ha _ hb he ↦ hg ha hb (Prod.mk.inj he).2)
  rw [he] at h
  linarith

lemma revealedEntropy_zero {ι α β : Type*} [Fintype ι] (p : PMF α)
    (hp : p.support.Finite) (s : α → β) (side : ι → α → Bool) (d : ι → ℝ) :
    revealedEntropy p hp s side d 0 = 0 := by
  unfold revealedEntropy
  rw [cutAverage_zero]
  have he : cutLabel side (fun _ ↦ false) = (fun _ _ ↦ false) := by
    funext a i
    simp [cutLabel]
  rw [he, averageStatisticConditionalEntropy_const]

theorem tendsto_revealedEntropy {ι α β : Type*} [Fintype ι] (p : PMF α)
    (hp : p.support.Finite) (s : α → β) (side : ι → α → Bool) (d : ι → ℝ)
    (hd : ∀ i, 0 < d i) (hsep : Set.InjOn (fun a i ↦ side i a) p.support) :
    Tendsto (revealedEntropy p hp s side d) atTop
      (𝓝 (finiteEntropy p hp - finiteEntropy (p.map s) (by simpa using hp.image s))) := by
  unfold revealedEntropy
  have h := tendsto_cutAverage d hd
    (fun c ↦ averageStatisticConditionalEntropy p hp s (cutLabel side c))
  have he : cutLabel side (fun _ ↦ true) = (fun a i ↦ side i a) := by
    funext a i
    simp [cutLabel]
  rw [he, averageStatisticConditionalEntropy_eq_sub_of_injective p hp s _ hsep] at h
  exact h

end ExactOverlaps.Entropy
