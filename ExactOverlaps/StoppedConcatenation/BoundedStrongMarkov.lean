/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.FreshSuffix

/-!
The Bernoulli suffix after an actual bounded stopping time has its original law
and is independent of the information available at that stopping time.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ExactOverlaps.StoppedConcatenation.BoundedStoppingRule

variable {ι : Type*} [MeasurableSpace ι] (T : BoundedStoppingRule ι)

theorem measure_eq_sum_time (μ : Measure (ℕ → ι)) (E : Set (ℕ → ι)) :
    μ E = ∑ n ∈ Finset.range (T.horizon + 1), μ (E ∩ {ω | T.time ω = n}) := by
  have hpre : T.time ⁻¹' (↑(Finset.range (T.horizon + 1)) : Set ℕ) = Set.univ := by
    ext ω
    simp only [Set.mem_preimage, Finset.mem_coe, Finset.mem_range, Set.mem_univ, iff_true]
    exact Nat.lt_succ_of_le (T.bounded ω)
  have h := sum_measure_preimage_singleton (μ := μ.restrict E)
    (Finset.range (T.horizon + 1))
    (fun n _ ↦ T.measurable_time (measurableSet_singleton n))
  rw [hpre, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] at h
  calc
    μ E = ∑ n ∈ Finset.range (T.horizon + 1), (μ.restrict E) (T.time ⁻¹' {n}) := h.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n _
      rw [Measure.restrict_apply (T.measurable_time (measurableSet_singleton n)), Set.inter_comm]
      rfl

theorem stopped_prefix_inter_suffix_measure (p : Measure ι) [IsProbabilityMeasure p]
    {E B : Set (ℕ → ι)}
    (hE : ∀ n, MeasurableSet[incrementFiltration (ι := ι) n] (E ∩ {ω | T.time ω = n}))
    (hB : MeasurableSet B) :
    Bernoulli.sequenceLaw p (E ∩ T.suffix ⁻¹' B) =
      Bernoulli.sequenceLaw p E * Bernoulli.sequenceLaw p B := by
  rw [T.measure_eq_sum_time (Bernoulli.sequenceLaw p) (E ∩ T.suffix ⁻¹' B)]
  calc
    _ = ∑ n ∈ Finset.range (T.horizon + 1),
        Bernoulli.sequenceLaw p (E ∩ {ω | T.time ω = n}) * Bernoulli.sequenceLaw p B := by
      apply Finset.sum_congr rfl
      intro n _
      have heq : (E ∩ T.suffix ⁻¹' B) ∩ {ω | T.time ω = n} =
          (E ∩ {ω | T.time ω = n}) ∩ (Bernoulli.shift^[n]) ⁻¹' B := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨⟨hω, hωB⟩, hn⟩
          exact ⟨⟨hω, hn⟩, by simpa only [suffix, hn] using hωB⟩
        · rintro ⟨⟨hω, hn⟩, hωB⟩
          exact ⟨⟨hω, by simpa only [suffix, hn] using hωB⟩, hn⟩
      rw [heq, prefix_inter_suffix_measure p n (hE n) hB]
    _ = _ := by
      rw [← Finset.sum_mul, ← T.measure_eq_sum_time (Bernoulli.sequenceLaw p) E]

theorem suffix_map (p : Measure ι) [IsProbabilityMeasure p] :
    (Bernoulli.sequenceLaw p).map T.suffix = Bernoulli.sequenceLaw p := by
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply T.measurable_suffix hB]
  have h := T.stopped_prefix_inter_suffix_measure p
    (E := Set.univ) (fun n ↦ by simpa using T.measurableSet_time_eq n) hB
  simpa only [Set.univ_inter, measure_univ, one_mul] using h

theorem stopped_sigma_inter_suffix_measure (p : Measure ι) [IsProbabilityMeasure p]
    {E B : Set (ℕ → ι)} (hE : MeasurableSet[T.adapted.measurableSpace] E)
    (hB : MeasurableSet B) :
    Bernoulli.sequenceLaw p (E ∩ T.suffix ⁻¹' B) =
      Bernoulli.sequenceLaw p E * Bernoulli.sequenceLaw p B := by
  apply T.stopped_prefix_inter_suffix_measure p _ hB
  intro n
  have hn := T.adapted.measurableSet_eq' n
  have h := (T.adapted.measurableSet_inter_eq_iff E n).1 (hE.inter hn)
  simpa using h

end ExactOverlaps.StoppedConcatenation.BoundedStoppingRule
