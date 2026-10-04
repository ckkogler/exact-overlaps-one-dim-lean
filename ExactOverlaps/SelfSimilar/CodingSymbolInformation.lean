module

public import ExactOverlaps.SelfSimilar.CodingLaw
public import ExactOverlaps.SelfSimilar.BernoulliPointwise

/-!
Symbol logarithmic weights along the genuine coding process. Symbols of
zero weight occur on a null set; no strictly positive weight assumption
is imposed on the system.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

noncomputable def headLogWeight (S : System ι) (ω : ℕ → ι) : ℝ :=
  Real.log (S.weight (ω 0) : ℝ)

theorem ae_alphabet_weight_pos (S : System ι) :
    ∀ᵐ i ∂S.alphabetLaw.toMeasure, 0 < (S.weight i : ℝ) := by
  rw [ae_iff]
  apply (S.alphabetLaw.toMeasure_apply_eq_zero_iff (Set.toFinite _).measurableSet).mpr
  apply Set.disjoint_left.mpr
  intro i hi hn
  have hp : 0 < (S.weight i : ℝ≥0∞) := (S.alphabetLaw.apply_pos_iff i).mpr hi
  exact hn (by exact_mod_cast hp)

theorem ae_coding_weight_pos (S : System ι) :
    ∀ᵐ ω ∂Bernoulli.sequenceLaw S.alphabetLaw.toMeasure,
      ∀ j : ℕ, 0 < (S.weight ((Bernoulli.shift^[j] ω) 0) : ℝ) := by
  have hh : ∀ᵐ ω ∂Bernoulli.sequenceLaw S.alphabetLaw.toMeasure, 0 < (S.weight (ω 0) : ℝ) := by
    have hmap : (Bernoulli.sequenceLaw S.alphabetLaw.toMeasure).map
        (fun ω : ℕ → ι ↦ ω 0) = S.alphabetLaw.toMeasure := Measure.infinitePi_map_eval _ _
    exact ae_of_ae_map (measurable_pi_apply 0).aemeasurable (hmap ▸ S.ae_alphabet_weight_pos)
  apply ae_all_iff.mpr
  intro j
  exact ((Bernoulli.measurePreserving_shift S.alphabetLaw.toMeasure).iterate j).quasiMeasurePreserving.ae hh

theorem measurable_headLogWeight (S : System ι) : Measurable S.headLogWeight :=
  (measurable_of_finite (fun i ↦ Real.log (S.weight i : ℝ))).comp (measurable_pi_apply 0)

theorem integrable_headLogWeight (S : System ι) :
    Integrable S.headLogWeight (Bernoulli.sequenceLaw S.alphabetLaw.toMeasure) := by
  obtain ⟨C, hC⟩ := (Set.finite_range (fun i ↦ |Real.log (S.weight i : ℝ)|)).bddAbove
  apply Integrable.of_bound S.measurable_headLogWeight.aestronglyMeasurable C
  exact ae_of_all _ (fun ω ↦ by
    simpa only [Real.norm_eq_abs, headLogWeight] using hC ⟨ω 0, rfl⟩)

theorem ae_headLogWeight_average (S : System ι) :
    ∀ᵐ ω ∂Bernoulli.sequenceLaw S.alphabetLaw.toMeasure,
      Tendsto (fun n ↦ birkhoffAverage ℝ Bernoulli.shift S.headLogWeight n ω)
        atTop (𝓝 (∫ v, S.headLogWeight v ∂Bernoulli.sequenceLaw S.alphabetLaw.toMeasure)) :=
  Bernoulli.ae_tendsto_birkhoffAverage S.alphabetLaw.toMeasure
    S.measurable_headLogWeight S.integrable_headLogWeight

end ExactOverlaps.SelfSimilar.System
