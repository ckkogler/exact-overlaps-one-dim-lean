/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.ConvolutionDisintegration.IntervalWidth

/-!
# Measurable admissible convolution families

Every fixed tuple coordinate is measurable. The interval-width condition is
therefore a measurable event on each finite-tuple component, and hence on
the full countable disjoint union with variable positive factor count.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set

namespace ExactOverlaps.ConvolutionDisintegration

lemma measurable_tupleCoordinate {α : Type*} [MeasurableSpace α] :
    ∀ n (i : Fin n), Measurable (fun w : Entropy.FiniteTuple α n ↦
      Entropy.tupleCoordinate n w i) := by
  intro n
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact measurable_fst
    · exact (ih j).comp measurable_snd

lemma measurableSet_admissible (r : ℝ) :
    MeasurableSet {c : FactorFamily | Admissible r c} := by
  change MeasurableSet[⨅ n, (inferInstance : MeasurableSpace
    (Entropy.FiniteTuple (ProbabilityMeasure ℝ) (n + 1))).map (Sigma.mk n)] _
  rw [MeasurableSpace.measurableSet_iInf]
  intro n
  change MeasurableSet {w : Entropy.FiniteTuple (ProbabilityMeasure ℝ) (n + 1) |
    ∀ j, HasIntervalWidth (Entropy.tupleCoordinate (n + 1) w j) r}
  simp only [ofPred_forall]
  exact MeasurableSet.iInter (fun j ↦
    measurable_tupleCoordinate (n + 1) j (measurableSet_hasIntervalWidth r))

lemma HasIntervalWidth.mono {μ : ProbabilityMeasure ℝ} {r s : ℝ}
    (h : HasIntervalWidth μ r) (hrs : r ≤ s) : HasIntervalWidth μ s := by
  obtain ⟨a, ha⟩ := h
  refine ⟨a, ha.mono (fun x hx ↦ ⟨hx.1, hx.2.trans (add_le_add le_rfl hrs)⟩)⟩

lemma Admissible.mono {r s : ℝ} {c : FactorFamily}
    (h : Admissible r c) (hrs : r ≤ s) : Admissible s c :=
  fun j ↦ (h j).mono hrs

end ExactOverlaps.ConvolutionDisintegration
