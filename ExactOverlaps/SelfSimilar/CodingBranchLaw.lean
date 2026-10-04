module

public import ExactOverlaps.SelfSimilar.CodingLaw
public import ExactOverlaps.SelfSimilar.BranchInformation
public import ExactOverlaps.SelfSimilar.BernoulliPointwise

/-!
The joint distribution of the first symbol and the coded point is the
sum of the actual branch measures. Consequently conditional branch
information is an integrable observable of the Bernoulli coding process.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem coding_branch_map (S : System ι) :
    (Bernoulli.sequenceLaw S.alphabetLaw.toMeasure).map (fun ω ↦ (ω 0, S.coding ω)) =
      ∑ i, (S.branchMeasure S.codingMeasure i).map (fun x ↦ (i, x)) := by
  let P := Bernoulli.sequenceLaw S.alphabetLaw.toMeasure
  let F : ι × (ℕ → ι) → ι × ℝ := fun z ↦ (z.1, S.map z.1 (S.coding z.2))
  have hmF : Measurable F := measurable_from_prod_countable_right
    (fun i ↦ measurable_const.prodMk ((S.map i).measurable.comp S.measurable_coding))
  have heq : (fun ω ↦ (ω 0, S.coding ω)) = F ∘ (fun ω ↦ (ω 0, Bernoulli.shift ω)) := by
    funext ω
    exact congrArg (Prod.mk (ω 0)) (S.coding_shift ω)
  rw [heq, ← Measure.map_map hmF ((measurable_pi_apply 0).prodMk Bernoulli.measurable_shift),
    Bernoulli.head_shift_map]
  apply Measure.ext
  intro E hE
  rw [Measure.map_apply hmF hE, Measure.prod_apply (hE.preimage hmF), lintegral_fintype,
    Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro i _
  have hmi : Measurable (fun x : ℝ ↦ (i, x)) := by fun_prop
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton i), alphabetLaw_apply,
    Measure.map_apply hmi hE,
    branchMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (S.map i).measurable (hE.preimage hmi),
    codingMeasure, Measure.map_apply S.measurable_coding]
  · exact mul_comm _ _
  · exact ((hE.preimage hmi).preimage (S.map i).measurable)

theorem integrable_coding_branch_observable (S : System ι) (g : ι → ℝ → ℝ)
    (hgm : ∀ i, Measurable (g i))
    (hgi : ∀ i, Integrable (g i) (S.branchMeasure S.codingMeasure i)) :
    Integrable (fun ω ↦ g (ω 0) (S.coding ω))
      (Bernoulli.sequenceLaw S.alphabetLaw.toMeasure) := by
  let f : ι × ℝ → ℝ := fun z ↦ g z.1 z.2
  have hm : Measurable f := measurable_from_prod_countable_right hgm
  have hi : Integrable f ((Bernoulli.sequenceLaw S.alphabetLaw.toMeasure).map
      (fun ω ↦ (ω 0, S.coding ω))) := by
    rw [coding_branch_map, integrable_finsetSum_measure]
    intro i _
    apply (integrable_map_measure hm.aestronglyMeasurable
      (measurable_const.prodMk measurable_id).aemeasurable).mpr
    simpa only [Function.comp_def, f, id_eq] using hgi i
  exact (integrable_map_measure hm.aestronglyMeasurable
    ((measurable_pi_apply 0).prodMk S.measurable_coding).aemeasurable).mp hi

theorem integrable_coding_branchInformation (S : System ι) :
    Integrable (fun ω ↦ S.branchInformation S.codingMeasure (ω 0) (S.coding ω))
      (Bernoulli.sequenceLaw S.alphabetLaw.toMeasure) :=
  S.integrable_coding_branch_observable (S.branchInformation S.codingMeasure)
    (S.measurable_branchInformation S.codingMeasure)
    (S.integrable_branchInformation S.codingMeasure_isStationary)

theorem ae_coding_branchInformation_average (S : System ι) :
    ∀ᵐ ω ∂Bernoulli.sequenceLaw S.alphabetLaw.toMeasure,
      Tendsto (fun n ↦ birkhoffAverage ℝ Bernoulli.shift
        (fun v ↦ S.branchInformation S.codingMeasure (v 0) (S.coding v)) n ω)
        atTop (𝓝 (∫ v, S.branchInformation S.codingMeasure (v 0) (S.coding v)
          ∂Bernoulli.sequenceLaw S.alphabetLaw.toMeasure)) := by
  apply Bernoulli.ae_tendsto_birkhoffAverage S.alphabetLaw.toMeasure _
    S.integrable_coding_branchInformation
  have hm : Measurable (fun z : ι × ℝ ↦ S.branchInformation S.codingMeasure z.1 z.2) :=
    measurable_from_prod_countable_right (S.measurable_branchInformation S.codingMeasure)
  exact hm.comp ((measurable_pi_apply 0).prodMk S.measurable_coding)

end ExactOverlaps.SelfSimilar.System
