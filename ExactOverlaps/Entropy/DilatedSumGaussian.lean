/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.Entropy.ContinuousSumGaussian
public import ExactOverlaps.Entropy.ContinuousSumDilation

/-!
# Quantitative Gaussian approximation after common dilation

The error is the common interval width times the dilation factor, multiplied
by the proved universal Gaussian constant. All laws and variances are actual
pushforwards and moments of the original finite family.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace ExactOverlaps.Entropy

open GaussianApproximation

theorem wasserstein1_dilated_continuousSumLaw_le {ι : Type*} [Fintype ι]
    (ν : ι → ProbabilityMeasure ℝ) (a b : ι → ℝ)
    (hab : ∀ i, ∀ᵐ x ∂(ν i : Measure ℝ), x ∈ Icc (a i) (b i))
    {c R : ℝ} (hc : 0 ≤ c) (hR : ∀ i, b i - a i ≤ R)
    (v : ℝ≥0) (hv : 0 < (v : ℝ))
    (hvariance : c ^ 2 * variance (id : ℝ → ℝ) (continuousSumLaw ν : Measure ℝ) = (v : ℝ)) :
    ∃ mean : ℝ, ∃ hi : Integrable (fun x : ℝ ↦ x)
      ((continuousSumLaw ν).map (fun x ↦ c * x) : Measure ℝ),
    wasserstein1 ((continuousSumLaw ν).map (fun x ↦ c * x)) (gaussianProbability mean v)
      hi (gaussianProbability_integrable_id mean v) ≤ gaussianApproximationConstant * (c * R) := by
  let ν' := fun i ↦ (ν i).map (fun x ↦ c * x)
  have hi (i : ι) : ∀ᵐ x ∂(ν' i : Measure ℝ), x ∈ Icc (c * a i) (c * b i) :=
    ae_map_mul_mem_Icc (ν i) hc (hab i)
  have hlen (i : ι) : c * b i - c * a i ≤ c * R := by
    simpa only [mul_sub] using mul_le_mul_of_nonneg_left (hR i) hc
  have hvar : (∑ i, variance (id : ℝ → ℝ) (ν' i : Measure ℝ)) = (v : ℝ) := by
    simp only [ν', variance_map_mul, ← Finset.mul_sum]
    rw [← variance_continuousSumLaw ν (fun i ↦ ⟨a i, b i, hab i⟩)]
    exact hvariance
  have h := wasserstein1_continuousSumLaw_le ν' (fun i ↦ c * a i) (fun i ↦ c * b i)
    hi hlen v hv hvar
  have he : continuousSumLaw ν' = (continuousSumLaw ν).map (fun x ↦ c * x) :=
    continuousSumLaw_map_mul ν c
  have hint := integrable_id_of_hasBoundedSupport _
    (continuousSumLaw_hasBoundedSupport ν' (fun i ↦ ⟨_, _, hi i⟩))
  rw [he] at hint
  refine ⟨∑ i, realLawMean (ν' i), hint, ?_⟩
  unfold wasserstein1 at h ⊢
  rw [he] at h
  exact h

end ExactOverlaps.Entropy
