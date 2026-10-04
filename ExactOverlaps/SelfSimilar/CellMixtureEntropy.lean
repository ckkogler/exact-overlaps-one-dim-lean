module

public import ExactOverlaps.Entropy.Mixture
public import ExactOverlaps.SelfSimilar.EntropySupport

/-!
Concavity inside an individual positive-mass cell of a finite mixture.
The posterior weights are the actual branch-cell masses divided by the
total cell mass. Null branch cells have weight zero, so their fallback
probability law never contributes to the inequality.
-/

@[expose] public section

open scoped Classical ENNReal BigOperators

namespace ExactOverlaps.Entropy

noncomputable def conditionalOrSelf {α β : Type*} (p : PMF α) (f : α → β) (b : β) : PMF α :=
  if h : b ∈ (p.map f).support then conditionalPMF p f ⟨b, h⟩ else p

theorem conditionalOrSelf_support_finite {α β : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (b : β) :
    (conditionalOrSelf p f b).support.Finite := by
  unfold conditionalOrSelf
  split_ifs with hb
  · exact conditionalPMF_support_finite p hp f ⟨b, hb⟩
  · exact hp

theorem marginal_mul_conditionalOrSelf {α β : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (b : β) (a : α) :
    ((p.map f) b).toReal * (conditionalOrSelf p f b a).toReal =
      if f a = b then (p a).toReal else 0 := by
  by_cases hb : b ∈ (p.map f).support
  · simp only [conditionalOrSelf, dite_eq_left hb]
    by_cases ha : f a = b
    · rw [ite_eq_left ha]
      exact marginal_toReal_mul_conditional p f ⟨b, hb⟩ ha
    · rw [conditionalPMF_toReal]
      simp only [ha, ite_false, mul_zero]
  · have hz : (p.map f) b = 0 := by
      change ¬ (p.map f) b ≠ 0 at hb
      exact not_not.mp hb
    simp only [conditionalOrSelf, dite_eq_right hb, hz, ENNReal.toReal_zero, zero_mul]
    by_cases ha : f a = b
    · rw [ite_eq_left ha]
      have hle := atom_toReal_le_marginal p hp f a
      rw [ha, hz, ENNReal.toReal_zero] at hle
      exact le_antisymm hle ENNReal.toReal_nonneg |>.symm
    · simp only [ha, ite_false]

theorem conditionalOrSelf_eq_of_constant {α β : Type*} (p : PMF α)
    (f : α → β) {c : β} (hc : ∀ a ∈ p.support, f a = c) (b : β) :
    conditionalOrSelf p f b = p := by
  have hmap : p.map f = PMF.pure c := by
    calc
      p.map f = p.map (fun _ ↦ c) := map_congr_on_support p (fun a ha ↦ hc a ha)
      _ = PMF.pure c := PMF.map_const _ _
  unfold conditionalOrSelf
  split_ifs with hb
  · have hbc : b = c := by simpa only [hmap, PMF.support_pure, Set.mem_singleton_iff] using hb
    ext a
    rw [conditionalPMF_apply]
    change (if f a = b then p a / (p.map f) b else 0) = p a
    rw [hmap, hbc]
    by_cases ha : a ∈ p.support
    · simp only [hc a ha, ite_true, PMF.pure_apply_self, div_one]
    · have hz : p a = 0 := by simpa using ha
      simp only [hz, PMF.pure_apply_self, div_one, ite_self]
  · rfl

theorem cell_mixture_entropy_concavity {ι α β : Type*} [Fintype ι]
    (p : PMF ι) (q : ι → PMF α) (hq : ∀ i, (q i).support.Finite)
    (f : α → β) (b : ((p.bind q).map f).support) :
    (∑ i, (p i).toReal * ((q i).map f b).toReal *
      finiteEntropy (conditionalOrSelf (q i) f b) (conditionalOrSelf_support_finite (q i) (hq i) f b)) ≤
    (((p.bind q).map f) b).toReal *
      finiteEntropy (conditionalPMF (p.bind q) f b)
        (conditionalPMF_support_finite _ (bind_support_finite p q hq) f b) := by
  let M : ℝ := (((p.bind q).map f) b).toReal
  have hM : 0 < M := marginal_toReal_pos (p.bind q) f b
  let w : ι → ℝ := fun i ↦ (p i).toReal * ((q i).map f b).toReal / M
  have hsum : (∑ i, (p i).toReal * ((q i).map f b).toReal) = M := by
    have he (c : β) : (((p.bind q).map f) c).toReal =
        ∑ i, (p i).toReal * ((q i).map f c).toReal := by
      rw [PMF.map_bind, bind_toReal]
    exact (he b).symm
  have hwsum : ∑ i, w i = 1 := by
    dsimp [w]
    rw [← Finset.sum_div, hsum, div_self hM.ne']
  have hmix (a : α) : (conditionalPMF (p.bind q) f b a).toReal =
      ∑ i, w i * (conditionalOrSelf (q i) f b a).toReal := by
    rw [conditionalPMF_toReal]
    have he (i : ι) : w i * (conditionalOrSelf (q i) f b a).toReal =
        (p i).toReal * (if f a = b then (q i a).toReal else 0) / M := by
      calc
        _ = (p i).toReal * (((q i).map f b).toReal *
            (conditionalOrSelf (q i) f b a).toReal) / M := by dsimp [w]; ring
        _ = _ := by rw [marginal_mul_conditionalOrSelf (q i) (hq i) f b a]
    simp_rw [he]
    rw [← Finset.sum_div]
    split_ifs with ha
    · rw [bind_toReal]
    · simp
  have hc := finiteEntropy_mixture_le w (fun i ↦ by dsimp [w]; positivity) hwsum
    (fun i ↦ conditionalOrSelf (q i) f b)
    (fun i ↦ conditionalOrSelf_support_finite (q i) (hq i) f b)
    (conditionalPMF (p.bind q) f b)
    (conditionalPMF_support_finite _ (bind_support_finite p q hq) f b) hmix
  have hmul := mul_le_mul_of_nonneg_left hc hM.le
  rw [Finset.mul_sum] at hmul
  convert hmul using 1
  apply Finset.sum_congr rfl
  intro i _
  dsimp [w]
  field_simp

end ExactOverlaps.Entropy
