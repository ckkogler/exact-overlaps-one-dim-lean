module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
# Local quadratic error and variance energy

All general energies take values in the extended nonnegative reals. A bounded
probability law need not have finite energy. Real-valued statements for finite
laws require a separate finiteness theorem before conversion to real numbers.

The local error is the infimum, over real centers, of the squared-distance
integral restricted to a half-open interval. This is the ordinary unnormalized
conditional variance, including the zero-mass case. Its identification with
mass times conditional variance is a separate proof obligation.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace ExactOverlaps.VarianceEnergy

/-- Squared-distance integral on the half-open interval `[a,a+r)`. -/
def localQuadraticError (μ : Measure ℝ) (a r c : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Ico a (a + r), ENNReal.ofReal ((x - c) ^ 2) ∂μ

/-- Minimum unnormalized local variance, with all real centers available. -/
def localVarianceMass (μ : Measure ℝ) (a r : ℝ) : ℝ≥0∞ :=
  ⨅ c : ℝ, localQuadraticError μ a r c

/-- Local variance, averaged over interval origins and normalized by `4/r³`. -/
def normalizedLocalVariance (μ : Measure ℝ) (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (4 / r ^ 3) * ∫⁻ a : ℝ, localVarianceMass μ a r

/-- Variance energy on the positive scales below `R`. -/
def energyBelow (μ : Measure ℝ) (R : ℝ) : ℝ≥0∞ :=
  ∫⁻ r in Ioo (0 : ℝ) R,
    normalizedLocalVariance μ r * ENNReal.ofReal (1 / r)

/-- Full variance energy on positive scales with logarithmic weight `dr/r`. -/
def energy (μ : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ r in Ioi (0 : ℝ),
    normalizedLocalVariance μ r * ENNReal.ofReal (1 / r)

lemma localVarianceMass_le (μ : Measure ℝ) (a r c : ℝ) :
    localVarianceMass μ a r ≤ localQuadraticError μ a r c :=
  iInf_le _ c

@[simp] lemma localQuadraticError_zero (a r c : ℝ) :
    localQuadraticError 0 a r c = 0 := by
  simp [localQuadraticError]

@[simp] lemma localVarianceMass_zero (a r : ℝ) :
    localVarianceMass 0 a r = 0 := by
  simp [localVarianceMass]

lemma localQuadraticError_add (μ ν : Measure ℝ) (a r c : ℝ) :
    localQuadraticError (μ + ν) a r c =
      localQuadraticError μ a r c + localQuadraticError ν a r c := by
  simp only [localQuadraticError, Measure.restrict_add, lintegral_add_measure]

lemma localQuadraticError_smul (t : ℝ≥0∞) (μ : Measure ℝ) (a r c : ℝ) :
    localQuadraticError (t • μ) a r c = t * localQuadraticError μ a r c := by
  simp only [localQuadraticError, Measure.restrict_smul, lintegral_smul_measure,
    smul_eq_mul]

/-- Taking a common center can only increase the sum of the separate minima. -/
lemma localVarianceMass_superadd (μ ν : Measure ℝ) (a r : ℝ) :
    localVarianceMass μ a r + localVarianceMass ν a r ≤
      localVarianceMass (μ + ν) a r := by
  apply le_iInf
  intro c
  rw [localQuadraticError_add]
  exact add_le_add (localVarianceMass_le μ a r c) (localVarianceMass_le ν a r c)

/-- Nonnegative scaling preserves the lower bound furnished by the infimum. -/
lemma smul_localVarianceMass_le (t : ℝ≥0∞) (μ : Measure ℝ) (a r : ℝ) :
    t * localVarianceMass μ a r ≤ localVarianceMass (t • μ) a r := by
  apply le_iInf
  intro c
  rw [localQuadraticError_smul]
  exact mul_le_mul_of_nonneg_left (localVarianceMass_le μ a r c) zero_le

/-- Concavity of local variance for nonnegative mixtures, before normalization. -/
lemma localVarianceMass_mixture_le (s t : ℝ≥0∞) (μ ν : Measure ℝ) (a r : ℝ) :
    s * localVarianceMass μ a r + t * localVarianceMass ν a r ≤
      localVarianceMass (s • μ + t • ν) a r := by
  exact (add_le_add (smul_localVarianceMass_le s μ a r)
    (smul_localVarianceMass_le t ν a r)).trans
      (localVarianceMass_superadd (s • μ) (t • ν) a r)

lemma localQuadraticError_mono {μ ν : Measure ℝ} (h : μ ≤ ν) (a r c : ℝ) :
    localQuadraticError μ a r c ≤ localQuadraticError ν a r c := by
  exact lintegral_mono' (Measure.restrict_mono (Subset.refl _) h) (le_refl _)

lemma localVarianceMass_mono {μ ν : Measure ℝ} (h : μ ≤ ν) (a r : ℝ) :
    localVarianceMass μ a r ≤ localVarianceMass ν a r := by
  exact iInf_mono (fun c ↦ localQuadraticError_mono h a r c)

lemma energyBelow_mono (μ : Measure ℝ) {R S : ℝ} (h : R ≤ S) :
    energyBelow μ R ≤ energyBelow μ S := by
  apply lintegral_mono' (Measure.restrict_mono _ le_rfl) (le_refl _)
  exact Ioo_subset_Ioo_right h

lemma energyBelow_le_energy (μ : Measure ℝ) (R : ℝ) :
    energyBelow μ R ≤ energy μ := by
  apply lintegral_mono' (Measure.restrict_mono _ le_rfl) (le_refl _)
  exact Ioo_subset_Ioi_self

end ExactOverlaps.VarianceEnergy
