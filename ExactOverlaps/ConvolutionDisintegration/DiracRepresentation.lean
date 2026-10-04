/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.ConvolutionDisintegration.FamilyRepresentation

/-!
# The actual one-factor Dirac disintegration

Every real probability law is the mixture of its point masses. This gives
an admissible positive-factor disintegration at every nonnegative scale,
with cost one, and proves that W takes values in the unit interval.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace ExactOverlaps.ConvolutionDisintegration

def singleLaw (μ : ProbabilityMeasure ℝ) : FactorFamily := ⟨0, (μ, PUnit.unit)⟩

lemma measurable_singleLaw : Measurable singleLaw :=
  (measurable_sigma_injection 0).comp (measurable_id.prodMk measurable_const)

lemma convolutionLaw_singleLaw (μ : ProbabilityMeasure ℝ) :
    convolutionLaw (singleLaw μ) = μ := Entropy.realConvolution_zero_right μ

lemma totalVariance_singleLaw (μ : ProbabilityMeasure ℝ) :
    totalVariance (singleLaw μ) = variance (id : ℝ → ℝ) (μ : Measure ℝ) := by
  change variance (id : ℝ → ℝ) (μ : Measure ℝ) + 0 = _
  exact add_zero _

lemma admissible_singleLaw_iff (μ : ProbabilityMeasure ℝ) (r : ℝ) :
    Admissible r (singleLaw μ) ↔ HasIntervalWidth μ r := by
  constructor
  · intro h; exact h 0
  · intro h j
    change Fin 1 at j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact h

def diracLaw (x : ℝ) : ProbabilityMeasure ℝ := ⟨Measure.dirac x, inferInstance⟩

def singleDirac (x : ℝ) : FactorFamily := singleLaw (diracLaw x)

lemma measurable_singleDirac : Measurable singleDirac :=
  measurable_singleLaw.comp measurable_dirac_law

lemma convolutionLaw_singleDirac (x : ℝ) :
    convolutionLaw (singleDirac x) = diracLaw x := convolutionLaw_singleLaw _

lemma admissible_singleDirac {r : ℝ} (hr : 0 ≤ r) (x : ℝ) :
    Admissible r (singleDirac x) := by
  apply (admissible_singleLaw_iff (diracLaw x) r).mpr
  refine ⟨x, ?_⟩
  change ∀ᵐ y ∂Measure.dirac x, y ∈ Icc x (x + r)
  have hx : x ∈ Icc x (x + r) := ⟨le_rfl, by linarith⟩
  simpa using hx

lemma cost_singleDirac (r x : ℝ) : cost r (singleDirac x) = 1 := by
  unfold cost singleDirac
  rw [totalVariance_singleLaw]
  change Real.exp (-4 / r ^ 2 * variance (id : ℝ → ℝ) (Measure.dirac x)) = 1
  simp only [variance_dirac, mul_zero, Real.exp_zero]

lemma familyMixture_singleDirac (μ : ProbabilityMeasure ℝ) :
    familyMixture μ singleDirac measurable_singleDirac = μ := by
  apply Subtype.ext
  change (μ : Measure ℝ).bind (fun x ↦
    (convolutionLaw (singleDirac x) : Measure ℝ)) = (μ : Measure ℝ)
  simp only [convolutionLaw_singleDirac, diracLaw]
  exact Measure.bind_dirac

def diracDisintegration (μ : ProbabilityMeasure ℝ) : ProbabilityMeasure FactorFamily :=
  μ.map singleDirac

lemma isDisintegration_dirac {r : ℝ} (hr : 0 ≤ r) (μ : ProbabilityMeasure ℝ) :
    IsDisintegration μ r (diracDisintegration μ) := by
  apply (isDisintegration_map_iff μ r μ singleDirac measurable_singleDirac).mpr
  exact ⟨familyMixture_singleDirac μ, Filter.Eventually.of_forall (admissible_singleDirac hr)⟩

lemma averageCost_dirac (r : ℝ) (μ : ProbabilityMeasure ℝ) :
    averageCost r (diracDisintegration μ) = 1 := by
  rw [diracDisintegration, averageCost_map_eq μ singleDirac measurable_singleDirac r]
  simp only [cost_singleDirac, integral_const]
  have hμ : (μ : Measure ℝ).real univ = 1 := by simp
  rw [hμ, one_smul]

lemma costValues_nonempty {r : ℝ} (hr : 0 ≤ r) (μ : ProbabilityMeasure ℝ) :
    (costValues μ r).Nonempty :=
  ⟨averageCost r (diracDisintegration μ), diracDisintegration μ,
    isDisintegration_dirac hr μ, rfl⟩

theorem W_nonneg {r : ℝ} (hr : 0 ≤ r) (μ : ProbabilityMeasure ℝ) : 0 ≤ W μ r := by
  apply le_csInf (costValues_nonempty hr μ)
  rintro _ ⟨θ, _, rfl⟩
  exact averageCost_nonneg r θ

theorem W_le_one {r : ℝ} (hr : 0 ≤ r) (μ : ProbabilityMeasure ℝ) : W μ r ≤ 1 := by
  exact (W_le_averageCost (isDisintegration_dirac hr μ)).trans_eq (averageCost_dirac r μ)

end ExactOverlaps.ConvolutionDisintegration
