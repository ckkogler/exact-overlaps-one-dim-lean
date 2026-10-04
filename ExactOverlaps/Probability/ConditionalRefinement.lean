module

public import ExactOverlaps.Probability.ConditionalMoments
import Mathlib.Tactic.FieldSimp

/-!
# Successive conditioning on finite observations

Conditioning first on one observation and then on another gives the actual
conditional probability law of the pair of observations. This supplies the
law-level interface for refinement of the cells of a cut partition.
-/

@[expose] public section

open scoped ENNReal Classical

namespace ExactOverlaps.Entropy

/-- A second observation of a conditional law has the normalized joint marginal. -/
lemma conditionalPMF_map_apply {α β γ : Type*} (p : PMF α) (f : α → β)
    (g : α → γ) (b : (p.map f).support) (c : γ) :
    ((conditionalPMF p f b).map g) c =
      (p.map (fun a ↦ (f a, g a))) (b, c) / (p.map f) b := by
  rw [PMF.map_apply, PMF.map_apply, div_eq_mul_inv, ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro a
  rw [conditionalPMF_apply]
  by_cases hf : f a = b <;> by_cases hg : g a = c <;>
    simp [hf, hg, Ne.symm, eq_comm, div_eq_mul_inv]

/-- Every positive atom after two observations is a positive joint atom. -/
lemma joint_mem_support_of_conditional {α β γ : Type*} (p : PMF α) (f : α → β)
    (g : α → γ) (b : (p.map f).support)
    (c : ((conditionalPMF p f b).map g).support) :
    (b.val, c.val) ∈ (p.map (fun a ↦ (f a, g a))).support := by
  obtain ⟨a, ha, hga⟩ := (PMF.mem_support_map_iff g (conditionalPMF p f b) c).mp c.property
  rw [conditionalPMF_support] at ha
  exact (PMF.mem_support_map_iff _ p _).mpr ⟨a, ha.2, Prod.ext ha.1 hga⟩

/-- Successive normalized restrictions are the normalized restriction to the joint fiber. -/
lemma conditionalPMF_conditionalPMF {α β γ : Type*} (p : PMF α) (f : α → β)
    (g : α → γ) (b : (p.map f).support)
    (c : ((conditionalPMF p f b).map g).support) :
    conditionalPMF (conditionalPMF p f b) g c =
      conditionalPMF p (fun a ↦ (f a, g a))
        ⟨(b.val, c.val), joint_mem_support_of_conditional p f g b c⟩ := by
  ext a
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [conditionalPMF_toReal, conditionalPMF_toReal, conditionalPMF_toReal,
    conditionalPMF_map_apply, ENNReal.toReal_div]
  have hb := (marginal_toReal_pos p f b).ne'
  by_cases hf : f a = b <;> by_cases hg : g a = c
  · simp only [hg, hf, ite_true]
    field_simp
  · simp [hf, hg]
  · simp [hf, hg]
  · simp [hf, hg]

/-- Equal positive fibers give the same conditional probability law, independent of labels. -/
lemma conditionalPMF_eq_of_fiber_eq {α β γ : Type*} (p : PMF α) (f : α → β)
    (g : α → γ) (b : (p.map f).support) (c : (p.map g).support)
    (h : ∀ a, f a = b ↔ g a = c) :
    conditionalPMF p f b = conditionalPMF p g c := by
  have hm : (p.map f) b = (p.map g) c := by
    rw [PMF.map_apply, PMF.map_apply]
    apply tsum_congr
    intro a
    by_cases hf : f a = b
    · have hg := (h a).mp hf
      simp [hf, hg]
    · have hg : g a ≠ c := fun hg ↦ hf ((h a).mpr hg)
      simp [hf, hg, Ne.symm]
  ext a
  simp only [conditionalPMF_apply, h a, hm]

/-- The conditional law of the observation fiber containing a positive atom. -/
noncomputable def conditionalAt {α β : Type*} (p : PMF α) (f : α → β)
    (a : p.support) : PMF α :=
  conditionalPMF p f ⟨f a, (PMF.mem_support_map_iff f p (f a)).mpr
    ⟨a, a.property, rfl⟩⟩

lemma mem_support_conditionalAt {α β : Type*} (p : PMF α) (f : α → β)
    (a : p.support) : a.val ∈ (conditionalAt p f a).support := by
  rw [conditionalAt, conditionalPMF_support]
  exact ⟨rfl, a.property⟩

lemma conditionalAt_eq_of_fiber_eq {α β γ : Type*} (p : PMF α) (f : α → β)
    (g : α → γ) (a : p.support) (h : ∀ x, f x = f a ↔ g x = g a) :
    conditionalAt p f a = conditionalAt p g a :=
  conditionalPMF_eq_of_fiber_eq p f g _ _ h

lemma conditionalAt_conditionalAt {α β γ : Type*} (p : PMF α) (f : α → β)
    (g : α → γ) (a : p.support) :
    conditionalAt (conditionalAt p f a) g ⟨a, mem_support_conditionalAt p f a⟩ =
      conditionalAt p (fun x ↦ (f x, g x)) a :=
  conditionalPMF_conditionalPMF p f g _ _

end ExactOverlaps.Entropy
