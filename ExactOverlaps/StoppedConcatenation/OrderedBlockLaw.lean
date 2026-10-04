/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.SequentialObservations
public import Mathlib.Data.Finset.Max

/-! Ordered genuine stopping blocks have the prescribed independent joint law. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Classical

namespace ExactOverlaps.StoppedConcatenation.BoundedStoppingRule

open SelfSimilar

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem measurable_block_after_start (S T : BoundedStoppingRule ι) :
    Measurable (fun ω ↦ T.stoppedWord (S.suffix ω)) :=
  (T.measurable_stoppedWord.mono T.adapted.measurableSpace_le le_rfl).comp S.measurable_suffix

theorem block_after_start_map (S T : BoundedStoppingRule ι) (p : PMF ι) :
    (Bernoulli.sequenceLaw p.toMeasure).map (fun ω ↦ T.stoppedWord (S.suffix ω)) =
      (T.stoppedWordLaw p).toMeasure := by
  change (Bernoulli.sequenceLaw p.toMeasure).map (T.stoppedWord ∘ S.suffix) = _
  rw [← Measure.map_map
    (T.measurable_stoppedWord.mono T.adapted.measurableSpace_le le_rfl) S.measurable_suffix,
    S.suffix_map, T.stoppedWordLaw_toMeasure]

theorem measurable_block_before_start (S T U : BoundedStoppingRule ι)
    (h : ∀ ω, (S.andThen T).time ω ≤ U.time ω) :
    Measurable[U.adapted.measurableSpace] (fun ω ↦ T.stoppedWord (S.suffix ω)) := by
  apply (S.measurable_at_andThen_right T T.stoppedWord T.measurable_stoppedWord).mono _ le_rfl
  apply (S.andThen T).adapted.measurableSpace_mono U.adapted
  intro ω
  change ((S.andThen T).time ω : WithTop ℕ) ≤ (U.time ω : WithTop ℕ)
  exact_mod_cast h ω

theorem independent_ordered_blocks {κ : Type*} [LinearOrder κ]
    (S τ : κ → BoundedStoppingRule ι) (p : PMF ι)
    (horder : ∀ i j, i < j → ∀ ω, ((S i).andThen (τ i)).time ω ≤ (S j).time ω) :
    iIndepFun (fun j ω ↦ (τ j).stoppedWord ((S j).suffix ω))
      (Bernoulli.sequenceLaw p.toMeasure) := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro I
  induction I using Finset.induction_on_max with
  | empty => intro E _; simp
  | insert j I hmax ih =>
    intro E hE
    have hnot : j ∉ I := fun hj ↦ lt_irrefl j (hmax j hj)
    have hEj := hE j (Finset.mem_insert_self j I)
    have hEI (i) (hi : i ∈ I) := hE i (Finset.mem_insert_of_mem hi)
    let A := ⋂ i ∈ I, (fun ω ↦ (τ i).stoppedWord ((S i).suffix ω)) ⁻¹' E i
    let B := (τ j).stoppedWord ⁻¹' E j
    have hA : MeasurableSet[(S j).adapted.measurableSpace] A := by
      apply MeasurableSet.biInter I.countable_toSet
      intro i hi
      exact (measurable_block_before_start (S i) (τ i) (S j) (horder i j (hmax i hi))) (hEI i hi)
    have hB : MeasurableSet B :=
      (τ j).measurable_stoppedWord.mono (τ j).adapted.measurableSpace_le le_rfl hEj
    have hprob : Bernoulli.sequenceLaw p.toMeasure ((S j).suffix ⁻¹' B) =
        Bernoulli.sequenceLaw p.toMeasure B := by
      rw [← Measure.map_apply (S j).measurable_suffix hB, (S j).suffix_map]
    have hi := ih hEI
    change Bernoulli.sequenceLaw p.toMeasure A = _ at hi
    simp only [Finset.mem_insert, Set.iInter_iInter_eq_or_left]
    rw [Finset.prod_insert hnot]
    calc
      _ = Bernoulli.sequenceLaw p.toMeasure (A ∩ (S j).suffix ⁻¹' B) := by
        congr 1
        ext ω
        simp only [A, B, Set.mem_inter_iff, Set.mem_preimage, and_comm]
      _ = Bernoulli.sequenceLaw p.toMeasure A * Bernoulli.sequenceLaw p.toMeasure B :=
        (S j).stopped_sigma_inter_suffix_measure p.toMeasure hA hB
      _ = _ := by rw [← hprob, hi]; exact mul_comm _ _

theorem ordered_blocks_joint_map {κ : Type*} [Fintype κ] [LinearOrder κ]
    (S τ : κ → BoundedStoppingRule ι) (p : PMF ι)
    (horder : ∀ i j, i < j → ∀ ω, ((S i).andThen (τ i)).time ω ≤ (S j).time ω) :
    (Bernoulli.sequenceLaw p.toMeasure).map (fun ω j ↦ (τ j).stoppedWord ((S j).suffix ω)) =
      Measure.pi (fun j ↦ ((τ j).stoppedWordLaw p).toMeasure) := by
  have h := (independent_ordered_blocks S τ p horder).map_fun_eq_pi_map
    (fun j ↦ (measurable_block_after_start (S j) (τ j)).aemeasurable)
  simpa only [block_after_start_map] using h

end ExactOverlaps.StoppedConcatenation.BoundedStoppingRule
