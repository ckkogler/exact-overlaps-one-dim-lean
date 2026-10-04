/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.Entropy.JointMixture
public import ExactOverlaps.Entropy.IndependentPair

/-!
If an additional record is sampled using only an observed label, revealing that
record does not further change the conditional law of the original data.
The statement concerns the actual PMF kernel mixture and its positive-mass labels.
-/

@[expose] public section

open scoped ENNReal Classical

namespace ExactOverlaps.StoppedConcatenation

open Entropy

variable {α β γ : Type*}

def recordLabel (f : α → β) (z : α × γ) : β × γ := (f z.1, z.2)

theorem jointMixture_map_recordLabel (p : PMF α) (f : α → β) (k : β → PMF γ) :
    (jointMixture p (fun a ↦ k (f a))).map (recordLabel f) = jointMixture (p.map f) k := by
  simp only [jointMixture, PMF.map_bind, PMF.map_comp, PMF.bind_map,
    Function.comp_def, recordLabel]

theorem recordLabel_mass (p : PMF α) (f : α → β) (k : β → PMF γ) (b : β × γ) :
    ((jointMixture p (fun a ↦ k (f a))).map (recordLabel f)) b = (p.map f) b.1 * k b.1 b.2 := by
  rw [jointMixture_map_recordLabel]
  exact jointMixture_apply _ _ b.1 b.2

def recordBaseLabel (p : PMF α) (f : α → β) (k : β → PMF γ)
    (b : ((jointMixture p (fun a ↦ k (f a))).map (recordLabel f)).support) :
    (p.map f).support :=
  ⟨b.val.1, by
    have hb := b.property
    rw [PMF.mem_support_iff, recordLabel_mass] at hb
    exact left_ne_zero_of_mul hb⟩

theorem recordKernelMass_ne_zero (p : PMF α) (f : α → β) (k : β → PMF γ)
    (b : ((jointMixture p (fun a ↦ k (f a))).map (recordLabel f)).support) :
    k b.val.1 b.val.2 ≠ 0 := by
  have hb := b.property
  rw [PMF.mem_support_iff, recordLabel_mass] at hb
  exact right_ne_zero_of_mul hb

theorem conditionalPMF_record_joint (p : PMF α) (f : α → β) (k : β → PMF γ)
    (b : ((jointMixture p (fun a ↦ k (f a))).map (recordLabel f)).support) :
    conditionalPMF (jointMixture p (fun a ↦ k (f a))) (recordLabel f) b =
      independentPair (conditionalPMF p f (recordBaseLabel p f k b)) (PMF.pure b.val.2) := by
  apply PMF.ext
  rintro ⟨a, c⟩
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  have hmass := recordLabel_mass p f k b.val
  have hbase := (marginal_toReal_pos p f (recordBaseLabel p f k b)).ne'
  have hk : (k b.val.1 b.val.2).toReal ≠ 0 :=
    (ENNReal.toReal_pos (recordKernelMass_ne_zero p f k b) ((k b.val.1).apply_ne_top b.val.2)).ne'
  by_cases ha : f a = b.val.1 <;> by_cases hc : c = b.val.2
  · simp [conditionalPMF_toReal, independentPair_apply, jointMixture_apply,
      ENNReal.toReal_mul, PMF.pure_apply, recordLabel, recordBaseLabel, ha, hc, hmass]
    field_simp [hk, hbase]
  · simp [conditionalPMF_toReal, independentPair_apply, jointMixture_apply,
      ENNReal.toReal_mul, PMF.pure_apply, recordLabel, recordBaseLabel, ha, hc]
    intro h
    exact (hc (congrArg Prod.snd h)).elim
  · simp [conditionalPMF_toReal, independentPair_apply, jointMixture_apply,
      ENNReal.toReal_mul, PMF.pure_apply, recordLabel, recordBaseLabel, ha, hc]
    intro h
    exact (ha (congrArg Prod.fst h)).elim
  · simp [conditionalPMF_toReal, independentPair_apply, jointMixture_apply,
      ENNReal.toReal_mul, PMF.pure_apply, recordLabel, recordBaseLabel, hc]
    intro h
    exact (ha (congrArg Prod.fst h)).elim

theorem conditionalPMF_record_fst (p : PMF α) (f : α → β) (k : β → PMF γ)
    (b : ((jointMixture p (fun a ↦ k (f a))).map (recordLabel f)).support) :
    (conditionalPMF (jointMixture p (fun a ↦ k (f a))) (recordLabel f) b).map Prod.fst =
      conditionalPMF p f (recordBaseLabel p f k b) := by
  rw [conditionalPMF_record_joint, independentPair_map_fst]

end ExactOverlaps.StoppedConcatenation
