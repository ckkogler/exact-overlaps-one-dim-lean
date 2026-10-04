module

public import ExactOverlaps.SelfSimilar.LogRatioConcentration
public import ExactOverlaps.SelfSimilar.EntropyBridge

/-!
The signed ratio law concentrates on absolute contractions near exp(n χ).
This is the geometric form of the finite-word weak law used in the
nonuniform-contraction argument. The minus sign of χ is retained explicitly.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal BigOperators Classical Topology

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι]

theorem logRatioDeviationProbability_eq_mass (S : System ι) (ε : ℝ) (n : ℕ) :
    ((S.wordLaw n).toOuterMeasure
      {w | (n : ℝ) * ε ≤ |S.centeredWordLogRatio n w|}).toReal =
      S.logRatioDeviationProbability ε n := by
  have hs : {w | (n : ℝ) * ε ≤ |S.centeredWordLogRatio n w|} =
      (Finset.univ.filter (fun w : Word ι n ↦
        (n : ℝ) * ε ≤ |S.centeredWordLogRatio n w|) : Set (Word ι n)) := by
    ext w
    simp
  rw [hs, PMF.toOuterMeasure_apply_finset,
    ENNReal.toReal_sum (fun w _ ↦ (S.wordLaw n).apply_ne_top w)]
  rfl

theorem wordRatio_typical_iff (S : System ι) (ε : ℝ) (n : ℕ) (w : Word ι n) :
    (Real.exp ((n : ℝ) * (S.lyapunov - ε)) < |S.wordRatio n w| ∧
      |S.wordRatio n w| < Real.exp ((n : ℝ) * (S.lyapunov + ε))) ↔
      |S.centeredWordLogRatio n w| < (n : ℝ) * ε := by
  have hr : 0 < |S.wordRatio n w| := abs_pos.mpr (S.wordRatio_ne_zero n w)
  rw [← Real.lt_log_iff_exp_lt hr, ← Real.log_lt_iff_lt_exp hr, abs_lt]
  simp only [centeredWordLogRatio, wordLogRatio]
  constructor <;> rintro ⟨hl, hu⟩ <;> constructor <;> nlinarith

/-- Atypical signed ratios, defined by an interval for their absolute values. -/
def atypicalRatioSet (S : System ι) (ε : ℝ) (n : ℕ) : Set ℝ :=
  {r | ¬ (Real.exp ((n : ℝ) * (S.lyapunov - ε)) < |r| ∧
      |r| < Real.exp ((n : ℝ) * (S.lyapunov + ε)))}

theorem measurableSet_atypicalRatioSet (S : System ι) (ε : ℝ) (n : ℕ) :
    MeasurableSet (S.atypicalRatioSet ε n) := by
  have habs : Measurable (fun r : ℝ ↦ |r|) := by fun_prop
  exact ((measurableSet_lt measurable_const habs).inter
    (measurableSet_lt habs measurable_const)).compl

theorem wordRatioLaw_atypical_mass (S : System ι) (ε : ℝ) (n : ℕ) :
    ((S.wordRatioLaw n).toMeasure (S.atypicalRatioSet ε n)).toReal =
      S.logRatioDeviationProbability ε n := by
  rw [PMF.toMeasure_apply_eq_toOuterMeasure_apply _ (S.measurableSet_atypicalRatioSet ε n),
    wordRatioLaw, PMF.toOuterMeasure_map_apply]
  have hs : S.wordRatio n ⁻¹' S.atypicalRatioSet ε n =
      {w | (n : ℝ) * ε ≤ |S.centeredWordLogRatio n w|} := by
    ext w
    simp only [Set.mem_preimage, atypicalRatioSet, Set.mem_ofPred_eq,
      S.wordRatio_typical_iff, not_lt]
  rw [hs]
  exact S.logRatioDeviationProbability_eq_mass ε n

/-- The law of large numbers at the Lyapunov scale for signed contraction classes. -/
theorem wordRatioLaw_atypical_mass_tendsto_zero (S : System ι) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ ↦
      ((S.wordRatioLaw n).toMeasure (S.atypicalRatioSet ε n)).toReal) atTop (𝓝 0) := by
  simp_rw [S.wordRatioLaw_atypical_mass]
  exact S.logRatioDeviationProbability_tendsto_zero hε

end ExactOverlaps.SelfSimilar.System
