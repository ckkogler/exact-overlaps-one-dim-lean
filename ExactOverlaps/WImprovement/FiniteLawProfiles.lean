/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.WImprovement.VarianceProfile
public import ExactOverlaps.Probability.FinitePoissonReal
public import ExactOverlaps.Entropy.Finite

/-!
# Finite probability averages of genuine variance profiles

The averaged profile uses the actual masses of a finite probability law.
Its logarithmic integral is exactly the weighted energy. A common finite
support yields a common positive small-scale cutoff for all components.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ExactOverlaps.WImprovement

open VarianceEnergy

variable {ι : Type*} [Fintype ι]

def meanVarianceProfile (q : PMF ι) (p : ι → PMF ℝ) (r : ℝ) : ℝ :=
  ∑ i, (q i).toReal * varianceProfile (p i).toMeasure r

def meanLogVarianceProfile (q : PMF ι) (p : ι → PMF ℝ) (R u : ℝ) : ℝ :=
  ∑ i, (q i).toReal * logVarianceProfile (p i).toMeasure R u

lemma meanVarianceProfile_nonneg (q : PMF ι) (p : ι → PMF ℝ) (r : ℝ) :
    0 ≤ meanVarianceProfile q p r :=
  Finset.sum_nonneg (fun _ _ ↦ mul_nonneg ENNReal.toReal_nonneg (varianceProfile_nonneg _ _))

lemma meanVarianceProfile_le_one (q : PMF ι) (p : ι → PMF ℝ) {r : ℝ} (hr : 0 < r) :
    meanVarianceProfile q p r ≤ 1 := by
  calc
    _ ≤ ∑ i, (q i).toReal * 1 := Finset.sum_le_sum (fun i _ ↦
      mul_le_mul_of_nonneg_left (varianceProfile_le_one (p i).toMeasure hr) ENNReal.toReal_nonneg)
    _ = 1 := by simpa only [mul_one] using Entropy.sum_pmf_toReal q

lemma meanLogVarianceProfile_eq (q : PMF ι) (p : ι → PMF ℝ) (R u : ℝ) :
    meanLogVarianceProfile q p R u =
      if Real.exp u < R then meanVarianceProfile q p (Real.exp u) else 0 := by
  by_cases h : Real.exp u < R
  · simp only [meanLogVarianceProfile, logVarianceProfile, ite_eq_left h, meanVarianceProfile]
  · simp only [meanLogVarianceProfile, logVarianceProfile, ite_eq_right h, mul_zero,
      Finset.sum_const_zero]

lemma meanLogVarianceProfile_nonneg (q : PMF ι) (p : ι → PMF ℝ) (R u : ℝ) :
    0 ≤ meanLogVarianceProfile q p R u :=
  Finset.sum_nonneg (fun _ _ ↦ mul_nonneg ENNReal.toReal_nonneg (logVarianceProfile_nonneg _ _ _))

lemma integrable_meanLogVarianceProfile (q : PMF ι) (p : ι → PMF ℝ)
    (hp : ∀ i, (p i).support.Finite) (R : ℝ) : Integrable (meanLogVarianceProfile q p R) := by
  exact integrable_finsetSum _ (fun i _ ↦
    (integrable_logVarianceProfile (p i).toMeasure
      (Poisson.finiteLaw_energy_ne_top (p i) (hp i)) R).const_mul (q i).toReal)

lemma integral_meanLogVarianceProfile (q : PMF ι) (p : ι → PMF ℝ)
    (hp : ∀ i, (p i).support.Finite) (R : ℝ) :
    (∫ u, meanLogVarianceProfile q p R u) =
      ∑ i, (q i).toReal * (energyBelow (p i).toMeasure R).toReal := by
  unfold meanLogVarianceProfile
  rw [integral_finsetSum _ (fun i _ ↦
    (integrable_logVarianceProfile (p i).toMeasure
      (Poisson.finiteLaw_energy_ne_top (p i) (hp i)) R).const_mul (q i).toReal)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul, integral_logVarianceProfile _ (Poisson.finiteLaw_energy_ne_top (p i) (hp i))]

lemma exists_common_vanishing_scale (p : ι → PMF ℝ) (hp : ∀ i, (p i).support.Finite) :
    ∃ δ > 0, ∀ i r, r ≤ δ → normalizedLocalVariance (p i).toMeasure r = 0 := by
  classical
  let s : Finset ℝ := Finset.univ.biUnion (fun i ↦ (hp i).toFinset)
  have hs (i : ι) : ∀ᵐ x ∂(p i).toMeasure, x ∈ s := by
    change (s : Set ℝ) ∈ ae (p i).toMeasure
    rw [mem_ae_iff_prob_eq_one s.measurableSet]
    apply (PMF.toMeasure_apply_eq_one_iff _ s.measurableSet).mpr
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simpa using hx⟩
  obtain ⟨δ, hδ, hsep⟩ := exists_pos_separation s
  exact ⟨δ, hδ, fun i r hr ↦ normalizedLocalVariance_eq_zero_of_separation
    (p i).toMeasure s (hs i) hsep hr⟩

lemma exists_meanLogVarianceProfile_cutoff (q : PMF ι) (p : ι → PMF ℝ)
    (hp : ∀ i, (p i).support.Finite) :
    ∃ δ > 0, ∀ R : ℝ, 0 < R → ∀ u : ℝ,
      u ≤ Real.log δ ∨ Real.log R ≤ u → meanLogVarianceProfile q p R u = 0 := by
  obtain ⟨δ, hδ, hv⟩ := exists_common_vanishing_scale p hp
  refine ⟨δ, hδ, ?_⟩
  intro R hR u hu
  apply Finset.sum_eq_zero
  intro i _
  rw [logVarianceProfile_eq_zero_of_cutoffs _ hδ hR (hv i) u hu, mul_zero]

end ExactOverlaps.WImprovement
