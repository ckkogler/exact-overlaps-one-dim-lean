/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.BoundedStrongMarkov

/-! Product laws for all genuine observables at a bounded stopping time. -/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ExactOverlaps.StoppedConcatenation.BoundedStoppingRule

variable {ι β : Type*} [MeasurableSpace ι] [MeasurableSpace β]

theorem independent_observable_suffix (T : BoundedStoppingRule ι)
    (p : Measure ι) [IsProbabilityMeasure p] (F : (ℕ → ι) → β)
    (hF : Measurable[T.adapted.measurableSpace] F) :
    IndepFun F T.suffix (Bernoulli.sequenceLaw p) := by
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro E B hE hB
  have h := T.stopped_sigma_inter_suffix_measure p (hF hE) hB
  have hb : Bernoulli.sequenceLaw p (T.suffix ⁻¹' B) = Bernoulli.sequenceLaw p B := by
    calc
      _ = ((Bernoulli.sequenceLaw p).map T.suffix) B :=
        (Measure.map_apply T.measurable_suffix hB).symm
      _ = _ := congrArg (fun μ : Measure (ℕ → ι) ↦ μ B) (T.suffix_map p)
  rw [hb]
  exact h

theorem observable_suffix_map (T : BoundedStoppingRule ι)
    (p : Measure ι) [IsProbabilityMeasure p] (F : (ℕ → ι) → β)
    (hF : Measurable[T.adapted.measurableSpace] F) :
    (Bernoulli.sequenceLaw p).map (fun ω ↦ (F ω, T.suffix ω)) =
      ((Bernoulli.sequenceLaw p).map F).prod (Bernoulli.sequenceLaw p) := by
  have hFm : Measurable F := hF.mono T.adapted.measurableSpace_le le_rfl
  rw [(T.independent_observable_suffix p F hF).map_prod_eq_prod_map_map
    hFm.aemeasurable T.measurable_suffix.aemeasurable, T.suffix_map p]

end ExactOverlaps.StoppedConcatenation.BoundedStoppingRule
