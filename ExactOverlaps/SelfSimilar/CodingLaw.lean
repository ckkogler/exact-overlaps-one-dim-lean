module

public import ExactOverlaps.SelfSimilar.CodingSeries
public import ExactOverlaps.SelfSimilar.BernoulliHeadTail
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
The distribution of the convergent affine coding series is a stationary
probability measure. Stationarity follows from the proved head-tail
product law, and does not enter as a property of the coding definition.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι]

noncomputable def alphabetLaw (S : System ι) : PMF ι :=
  PMF.ofFintype (fun i ↦ (S.weight i : ℝ≥0∞)) S.weight_sum_ennreal

@[simp] theorem alphabetLaw_apply (S : System ι) (i : ι) :
    S.alphabetLaw i = (S.weight i : ℝ≥0∞) := rfl

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

noncomputable def codingMeasure (S : System ι) : Measure ℝ :=
  (Bernoulli.sequenceLaw S.alphabetLaw.toMeasure).map S.coding

instance (S : System ι) : IsProbabilityMeasure S.codingMeasure := by
  unfold codingMeasure
  exact (Measure.isProbabilityMeasure_map_iff S.measurable_coding.aemeasurable).2 inferInstance

theorem codingMeasure_isStationary (S : System ι) : S.IsStationary S.codingMeasure := by
  let P := Bernoulli.sequenceLaw S.alphabetLaw.toMeasure
  let F : ι × (ℕ → ι) → ℝ := fun z ↦ S.map z.1 (S.coding z.2)
  have hmF : Measurable F := measurable_from_prod_countable_right
    (fun i ↦ (S.map i).measurable.comp S.measurable_coding)
  have hmap : S.codingMeasure = (S.alphabetLaw.toMeasure.prod P).map F := by
    have heq : S.coding = F ∘ (fun ω ↦ (ω 0, Bernoulli.shift ω)) := by
      funext ω
      exact S.coding_shift ω
    change P.map S.coding = _
    rw [heq, ← Measure.map_map hmF ((measurable_pi_apply 0).prodMk Bernoulli.measurable_shift)]
    exact congrArg (Measure.map F) (Bernoulli.head_shift_map S.alphabetLaw.toMeasure)
  apply Measure.ext
  intro E hE
  change S.codingMeasure E = (∑ i, (S.weight i : ℝ≥0∞) • S.codingMeasure.map (S.map i)) E
  conv_lhs => rw [hmap, Measure.map_apply hmF hE,
    Measure.prod_apply (hE.preimage hmF), lintegral_fintype]
  rw [Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton i), alphabetLaw_apply,
    Measure.smul_apply, smul_eq_mul, Measure.map_apply (S.map i).measurable hE]
  change P {ω | S.map i (S.coding ω) ∈ E} * (S.weight i : ℝ≥0∞) =
    (S.weight i : ℝ≥0∞) * S.codingMeasure ((S.map i) ⁻¹' E)
  rw [codingMeasure, Measure.map_apply S.measurable_coding (hE.preimage (S.map i).measurable)]
  exact mul_comm _ _

end ExactOverlaps.SelfSimilar.System
