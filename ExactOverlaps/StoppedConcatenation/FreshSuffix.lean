/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.StoppingRules
public import ExactOverlaps.SelfSimilar.BernoulliHeadTail

/-! The actual fresh-suffix law at every deterministic increment time. -/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ExactOverlaps.StoppedConcatenation

variable {ι : Type*} [MeasurableSpace ι]

theorem independent_prefix_suffix (p : Measure ι) [IsProbabilityMeasure p] (n : ℕ) :
    Indep (incrementFiltration (ι := ι) n)
      (MeasurableSpace.comap (Bernoulli.shift^[n]) inferInstance) (Bernoulli.sequenceLaw p) := by
  let σ : ℕ → MeasurableSpace (ℕ → ι) :=
    fun k ↦ MeasurableSpace.comap (fun ω : ℕ → ι ↦ ω k) inferInstance
  have hind : iIndepFun (fun k (ω : ℕ → ι) ↦ ω k) (Bernoulli.sequenceLaw p) :=
    iIndepFun_infinitePi (X := fun _ x ↦ x) (fun _ ↦ measurable_id)
  have hσ : ∀ k, σ k ≤ (inferInstance : MeasurableSpace (ℕ → ι)) :=
    fun k ↦ (measurable_pi_apply k).comap_le
  have hs := indep_biSup_compl hσ hind.iIndep (Set.Iio n)
  apply indep_of_indep_of_le hs
  · change (⨆ k : Fin n, σ k) ≤ _
    apply iSup_le
    intro k
    exact le_iSup_of_le (k : ℕ) (le_iSup_of_le k.isLt le_rfl)
  · have heq : (Bernoulli.shift^[n] : (ℕ → ι) → (ℕ → ι)) =
        fun ω k ↦ ω (k + n) := by
      funext ω k
      exact Bernoulli.shift_iterate n ω k
    rw [heq, MeasurableSpace.comap_process_pi]
    apply iSup_le
    intro k
    exact le_iSup_of_le (k + n) (le_iSup_of_le (by simp : k + n ∈ (Set.Iio n)ᶜ) le_rfl)

theorem prefix_inter_suffix_measure (p : Measure ι) [IsProbabilityMeasure p]
    (n : ℕ) {E B : Set (ℕ → ι)}
    (hE : MeasurableSet[incrementFiltration (ι := ι) n] E) (hB : MeasurableSet B) :
    Bernoulli.sequenceLaw p (E ∩ (Bernoulli.shift^[n]) ⁻¹' B) =
      Bernoulli.sequenceLaw p E * Bernoulli.sequenceLaw p B := by
  have ht : MeasurableSet[MeasurableSpace.comap (Bernoulli.shift^[n]) inferInstance]
      ((Bernoulli.shift^[n]) ⁻¹' B) :=
    MeasurableSpace.measurableSet_comap.mpr ⟨B, hB, rfl⟩
  rw [((independent_prefix_suffix p n).indepSet_of_measurableSet hE ht).measure_inter_eq_mul]
  have hp := (Bernoulli.measurePreserving_shift p).iterate n
  have hb : Bernoulli.sequenceLaw p ((Bernoulli.shift^[n]) ⁻¹' B) =
      Bernoulli.sequenceLaw p B := by
    calc
      _ = ((Bernoulli.sequenceLaw p).map (Bernoulli.shift^[n])) B :=
        (Measure.map_apply (Bernoulli.measurable_shift.iterate n) hB).symm
      _ = _ := congrArg (fun μ : Measure (ℕ → ι) ↦ μ B) hp.map_eq
  rw [hb]

namespace BoundedStoppingRule

variable (T : BoundedStoppingRule ι)

theorem measurableSet_time_eq (n : ℕ) :
    MeasurableSet[incrementFiltration (ι := ι) n] {ω | T.time ω = n} := by
  simpa using T.adapted.measurableSet_eq n

theorem measurable_time : Measurable T.time := by
  apply measurable_to_countable'
  intro n
  exact incrementFiltration.le n _ (T.measurableSet_time_eq n)

def suffix (ω : ℕ → ι) : ℕ → ι := Bernoulli.shift^[T.time ω] ω

theorem measurable_suffix : Measurable T.suffix := by
  have hm : Measurable (fun z : (ℕ → ι) × ℕ ↦ Bernoulli.shift^[z.2] z.1) :=
    measurable_from_prod_countable_left (fun n ↦ Bernoulli.measurable_shift.iterate n)
  exact hm.comp (measurable_id.prodMk T.measurable_time)

end BoundedStoppingRule
end ExactOverlaps.StoppedConcatenation
