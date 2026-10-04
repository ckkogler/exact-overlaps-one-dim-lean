module

public import ExactOverlaps.SelfSimilar.RatioLevels

/-!
Concentration of the actual signed ratio-class law at its integer Lyapunov
level, including the equivalent sum of genuine positive-class masses.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators Classical

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι]

theorem wordRatioLaw_atypical_level_mass_le (S : System ι) {ε : ℝ} {n : ℕ}
    (hn : 2 ≤ ε * (n : ℝ)) :
    ((S.wordRatioLaw n).toMeasure (S.atypicalRatioLevelSet ε n)).toReal ≤
      S.logRatioDeviationProbability (ε * Real.log 2 / 2) n := by
  rw [PMF.toMeasure_apply_eq_toOuterMeasure_apply _
    (S.measurableSet_atypicalRatioLevelSet ε n), wordRatioLaw,
    PMF.toOuterMeasure_map_apply]
  let E : Set (Word ι n) :=
    {w | (n : ℝ) * (ε * Real.log 2 / 2) ≤ |S.centeredWordLogRatio n w|}
  have hsub : S.wordRatio n ⁻¹' S.atypicalRatioLevelSet ε n ⊆ E := by
    intro w hw
    change (n : ℝ) * (ε * Real.log 2 / 2) ≤ |S.centeredWordLogRatio n w|
    apply le_of_not_gt
    intro hgood
    exact hw (S.wordRatio_level_typical hn w hgood)
  have hfinite : (S.wordLaw n).toOuterMeasure E ≠ ⊤ := by
    rw [PMF.toOuterMeasure_apply]
    exact (S.wordLaw n).tsum_coe_indicator_ne_top E
  exact (ENNReal.toReal_mono hfinite ((S.wordLaw n).toOuterMeasure.mono hsub)).trans_eq
    (S.logRatioDeviationProbability_eq_mass (ε * Real.log 2 / 2) n)

theorem wordRatioLaw_atypical_level_mass_tendsto_zero (S : System ι)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ ↦
      ((S.wordRatioLaw n).toMeasure (S.atypicalRatioLevelSet ε n)).toReal) atTop (𝓝 0) := by
  have hupper := S.logRatioDeviationProbability_tendsto_zero
    (show 0 < ε * Real.log 2 / 2 from
      div_pos (mul_pos hε (Real.log_pos (by norm_num))) (by norm_num))
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg) _ hupper
  have hev : ∀ᶠ n : ℕ in atTop, 2 / ε ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hev] with n hn
  apply S.wordRatioLaw_atypical_level_mass_le
  have h := (div_le_iff₀ hε).mp hn
  nlinarith

theorem wordRatioLaw_typical_level_mass_tendsto_one (S : System ι)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ ↦
      ((S.wordRatioLaw n).toMeasure (S.atypicalRatioLevelSet ε n)ᶜ).toReal) atTop (𝓝 1) := by
  have h := tendsto_const_nhds.sub (S.wordRatioLaw_atypical_level_mass_tendsto_zero hε)
    (a := (1 : ℝ))
  have he (n : ℕ) : ((S.wordRatioLaw n).toMeasure (S.atypicalRatioLevelSet ε n)ᶜ).toReal =
      1 - ((S.wordRatioLaw n).toMeasure (S.atypicalRatioLevelSet ε n)).toReal := by
    change (S.wordRatioLaw n).toMeasure.real (S.atypicalRatioLevelSet ε n)ᶜ =
      1 - (S.wordRatioLaw n).toMeasure.real (S.atypicalRatioLevelSet ε n)
    rw [measureReal_compl (S.measurableSet_atypicalRatioLevelSet ε n), probReal_univ]
  simp_rw [he]
  simpa only [sub_zero] using h

/-- Any measurable class event has exactly its finite sum of positive class masses. -/
theorem wordRatioLaw_mass_eq_support_sum (S : System ι) (n : ℕ)
    (E : Set ℝ) (hE : MeasurableSet E) :
    ((S.wordRatioLaw n).toMeasure E).toReal =
      (letI : Fintype (S.wordRatioLaw n).support := (S.wordRatioLaw_support_finite n).fintype
      ∑ r : (S.wordRatioLaw n).support, if (r : ℝ) ∈ E then (S.wordRatioLaw n r).toReal else 0) := by
  classical
  let : Fintype (S.wordRatioLaw n).support := (S.wordRatioLaw_support_finite n).fintype
  rw [PMF.toMeasure_apply_eq_toOuterMeasure_apply _ hE]
  have he : (S.wordRatioLaw n).toOuterMeasure E =
      (Entropy.supportLaw (S.wordRatioLaw n)).toOuterMeasure
        {r : (S.wordRatioLaw n).support | (r : ℝ) ∈ E} := by
    conv_lhs => rw [← Entropy.supportLaw_map_val (S.wordRatioLaw n)]
    rw [PMF.toOuterMeasure_map_apply]
    rfl
  rw [he, PMF.toOuterMeasure_apply_fintype, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro r _
    by_cases hr : (r : ℝ) ∈ E <;> simp [Set.indicator, hr, Entropy.supportLaw_apply]
  · intro r _
    by_cases hr : (r : ℝ) ∈ E <;> simp [Set.indicator, hr, Entropy.supportLaw_apply,
      (S.wordRatioLaw n).apply_ne_top]

/-- In the actual finite list of positive ratio classes, typical total weight tends to one. -/
theorem wordRatioLaw_typical_level_support_sum_tendsto_one (S : System ι)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ ↦
      letI : Fintype (S.wordRatioLaw n).support := (S.wordRatioLaw_support_finite n).fintype
      ∑ r : (S.wordRatioLaw n).support,
        if (S.dyadicLyapunov - ε) * n ≤ (ratioLevel r : ℝ) ∧
            (ratioLevel r : ℝ) ≤ (S.dyadicLyapunov + ε) * n
        then (S.wordRatioLaw n r).toReal else 0) atTop (𝓝 1) := by
  have h := S.wordRatioLaw_typical_level_mass_tendsto_one hε
  convert h using 1
  funext n
  rw [S.wordRatioLaw_mass_eq_support_sum n _
    (S.measurableSet_atypicalRatioLevelSet ε n).compl]
  simp only [atypicalRatioLevelSet, Set.mem_compl_iff, Set.mem_ofPred_eq, not_not]

end ExactOverlaps.SelfSimilar.System
