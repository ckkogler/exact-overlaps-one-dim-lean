/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.HeadContinuation
public import ExactOverlaps.StoppedConcatenation.DependentSuffixAE

/-! Actual starts inside a selected continuation retain ordering after the common head block. -/

@[expose] public section

open MeasureTheory
open scoped Classical

namespace ExactOverlaps.StoppedConcatenation

open SelfSimilar Entropy

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem headContinuation_time (S : System ι) (G T : BoundedStoppingRule ι)
    (A : (headLabelLaw S G T).support → BoundedStoppingRule ι) (ω : ℕ → ι) :
    (headContinuation S G T A).time ω = (G.andThen T).time ω +
      (supportedRule (headLabelLaw S G T) A
        (headLabel S (G.stoppedWord ω, T.stoppedWord (G.suffix ω)))).time ((G.andThen T).suffix ω) := rfl

theorem headContinuation_suffix (S : System ι) (G T : BoundedStoppingRule ι)
    (A : (headLabelLaw S G T).support → BoundedStoppingRule ι) (ω : ℕ → ι) :
    (headContinuation S G T A).suffix ω =
      (supportedRule (headLabelLaw S G T) A
        (headLabel S (G.stoppedWord ω, T.stoppedWord (G.suffix ω)))).suffix ((G.andThen T).suffix ω) :=
  (G.andThen T).suffix_andThenChoice
    (fun ω ↦ (G.stoppedWord ω, T.stoppedWord (G.suffix ω))) (G.measurable_sequentialWords T)
    (fun z ↦ supportedRule (headLabelLaw S G T) A (headLabel S z))
    (supportedRuleHorizon _ (headLabelLaw_support_finite S G T) A)
    (fun z ↦ supportedRule_horizon_le _ _ A (headLabel S z)) ω

theorem headContinuation_time_congr (S : System ι) (G T : BoundedStoppingRule ι)
    (A B : (headLabelLaw S G T).support → BoundedStoppingRule ι)
    (h : ∀ b ω, (A b).time ω = (B b).time ω) (ω : ℕ → ι) :
    (headContinuation S G T A).time ω = (headContinuation S G T B).time ω := by
  rw [headContinuation_time, headContinuation_time]
  congr 1
  unfold supportedRule
  split_ifs
  · exact h _ _
  · rfl

theorem headContinuation_after_head (S : System ι) (G T : BoundedStoppingRule ι)
    (A : (headLabelLaw S G T).support → BoundedStoppingRule ι) (ω : ℕ → ι) :
    (G.andThen T).time ω ≤ (headContinuation S G T A).time ω :=
  Nat.le_add_right _ _

theorem headContinuation_ordered_ae (S : System ι) (G T U : BoundedStoppingRule ι)
    (A B : (headLabelLaw S G T).support → BoundedStoppingRule ι)
    (h : ∀ b, ∀ᵐ ω ∂Bernoulli.sequenceLaw S.alphabetLaw.toMeasure,
      ((A b).andThen U).time ω ≤ (B b).time ω) :
    ∀ᵐ ω ∂Bernoulli.sequenceLaw S.alphabetLaw.toMeasure,
      ((headContinuation S G T A).andThen U).time ω ≤ (headContinuation S G T B).time ω := by
  let F := fun ω ↦ (G.stoppedWord ω, T.stoppedWord (G.suffix ω))
  let P := fun (z : (Σ n : ℕ, Word ι n) × (Σ n : ℕ, Word ι n)) (ω : ℕ → ι) ↦
    ((supportedRule (headLabelLaw S G T) A (headLabel S z)).andThen U).time ω ≤
      (supportedRule (headLabelLaw S G T) B (headLabel S z)).time ω
  have hp : ∀ z, MeasurableSet {ω | P z ω} := fun z ↦
    measurableSet_le ((supportedRule (headLabelLaw S G T) A (headLabel S z)).andThen U).measurable_time
      (supportedRule (headLabelLaw S G T) B (headLabel S z)).measurable_time
  have hP : ∀ z ∈ (independentPair (G.stoppedWordLaw S.alphabetLaw)
      (T.stoppedWordLaw S.alphabetLaw)).support,
      ∀ᵐ ω ∂Bernoulli.sequenceLaw S.alphabetLaw.toMeasure, P z ω := by
    intro z hz
    have hb : headLabel S z ∈ (headLabelLaw S G T).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨z, hz, rfl⟩
    let b : (headLabelLaw S G T).support := ⟨headLabel S z, hb⟩
    have hA : supportedRule (headLabelLaw S G T) A (headLabel S z) = A b := supportedRule_at _ _ b
    have hB : supportedRule (headLabelLaw S G T) B (headLabel S z) = B b := supportedRule_at _ _ b
    simpa only [P, hA, hB] using h b
  have ht := (G.andThen T).dependent_suffix_ae S.alphabetLaw F (G.measurable_sequentialWords T)
    (independentPair (G.stoppedWordLaw S.alphabetLaw) (T.stoppedWordLaw S.alphabetLaw))
    (G.sequential_stoppedWord_map T S.alphabetLaw) P hp hP
  filter_upwards [ht] with ω hω
  change (headContinuation S G T A).time ω + U.time ((headContinuation S G T A).suffix ω) ≤ _
  rw [headContinuation_time, headContinuation_time, headContinuation_suffix]
  change ((supportedRule (headLabelLaw S G T) A (headLabel S (F ω))).time ((G.andThen T).suffix ω) +
      U.time ((supportedRule (headLabelLaw S G T) A (headLabel S (F ω))).suffix ((G.andThen T).suffix ω))) ≤
    (supportedRule (headLabelLaw S G T) B (headLabel S (F ω))).time ((G.andThen T).suffix ω) at hω
  dsimp only [F] at hω
  omega

end ExactOverlaps.StoppedConcatenation
