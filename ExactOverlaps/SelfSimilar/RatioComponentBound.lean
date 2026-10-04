module

public import ExactOverlaps.SelfSimilar.ComponentEntropyBound
public import ExactOverlaps.SelfSimilar.VariableRatioComponents

/-!
A finite expectation estimate separating ratio classes where the inverse
theorem applies from a proved small exceptional mass. All component levels
may depend on the ratio, between the common conditioning and target levels.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators Classical

namespace ExactOverlaps.Entropy

theorem average_component_entropy_trivial_bound (ν τ : ProbabilityMeasure ℝ)
    (hν : HasBoundedSupport ν) (hτ : HasBoundedSupport τ) (i : ℤ) (m : ℕ)
    {γ : ℝ} (hγ : 0 ≤ γ) :
    γ * averageRawComponentEntropy ν hν i m ≤ γ * ((m : ℝ) * Real.log 2) +
      averageRawLeftConvolutionEntropy ν τ hν hτ i m - dyadicEntropy τ hτ (i + m) + Real.log 2 := by
  have hraw : averageRawComponentEntropy ν hν i m ≤ (m : ℝ) * Real.log 2 := by
    rw [averageRawComponentEntropy_eq_sub]
    exact dyadicEntropy_increment_le ν hν i m
  have hmono := dyadicEntropy_right_le_averageRawLeftConvolutionEntropy_add ν τ hν hτ i m
  have h := mul_le_mul_of_nonneg_left hraw hγ
  linarith

end ExactOverlaps.Entropy

namespace ExactOverlaps.SelfSimilar.System

open Entropy
variable {ι : Type*} [Fintype ι]

noncomputable def ratioClassBadMass (S : System ι) (n : ℕ)
    (G : Finset (S.wordRatioLaw n).support) : ℝ :=
  letI : Fintype (S.wordRatioLaw n).support := (S.wordRatioLaw_support_finite n).fintype
  ∑ r : (S.wordRatioLaw n).support, if r ∈ G then 0 else (S.wordRatioLaw n r).toReal

theorem exists_ratio_component_entropy_bound (S : System ι) (μ : ProbabilityMeasure ℝ)
    (hμ : S.IsStationary (μ : Measure ℝ))
    (hdim : (lowerHausdorffDimension (μ : Measure ℝ)).toReal < 1) {e : ℝ} (he : 0 < e) :
    ∃ γ > 0, ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ,
      ∀ j : (S.wordRatioLaw n).support → ℤ, ∀ i f : ℤ, i ≤ f →
      (∀ r, i ≤ j r) → (∀ r, j r ≤ f) → ∀ G : Finset (S.wordRatioLaw n).support,
      (∀ r ∈ G, N ≤ (f - j r).toNat ∧
        (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (j r) * |(r : ℝ)| ∧ (2 : ℝ) ^ (j r) * |(r : ℝ)| ≤ 1) →
      γ * S.averageVariableRatioTranslationEntropy n j f ≤
        γ * (e + S.ratioClassBadMass n G) * (((f - i : ℤ) : ℝ) * Real.log 2) +
        (dyadicEntropy μ (S.hasBoundedSupport hμ) f - dyadicEntropy μ (S.hasBoundedSupport hμ) i) -
        S.averageRatioScaledEntropy μ (S.hasBoundedSupport hμ) n f +
        S.averageRatioScaledEntropy μ (S.hasBoundedSupport hμ) n i + 2 * Real.log 2 := by
  obtain ⟨γ, hγ, N, hN, hgain⟩ := S.exists_average_component_entropy_bound μ hμ hdim he
  refine ⟨γ, hγ, N, hN, ?_⟩
  intro n j i f hif hij hjf G hgood
  let : Fintype (S.wordRatioLaw n).support := (S.wordRatioLaw_support_finite n).fintype
  let p := supportLaw (S.wordRatioLaw n)
  let D : ℝ := ((f - i : ℤ) : ℝ) * Real.log 2
  have hD : 0 ≤ D := mul_nonneg (by exact_mod_cast sub_nonneg.mpr hif) (Real.log_nonneg (by norm_num))
  let H (r : (S.wordRatioLaw n).support) := averageRawComponentEntropy (S.ratioTranslationProbability n r)
    (S.ratioTranslationProbability_hasBoundedSupport n r) (j r) (f - j r).toNat
  let C (r : (S.wordRatioLaw n).support) := averageRawLeftConvolutionEntropy
    (S.ratioTranslationProbability n r) (S.ratioScaledProbability μ n r)
    (S.ratioTranslationProbability_hasBoundedSupport n r)
    (S.ratioScaledProbability_hasBoundedSupport μ (S.hasBoundedSupport hμ) n r) (j r) (f - j r).toNat
  let T (r : (S.wordRatioLaw n).support) := dyadicEntropy (S.ratioScaledProbability μ n r)
    (S.ratioScaledProbability_hasBoundedSupport μ (S.hasBoundedSupport hμ) n r) f
  have hlevel (r : (S.wordRatioLaw n).support) : j r + ((f - j r).toNat : ℤ) = f := by
    have := hjf r
    omega
  have hdepth (r : (S.wordRatioLaw n).support) :
      ((f - j r).toNat : ℝ) * Real.log 2 ≤ D := by
    have hcast : ((f - j r).toNat : ℝ) = ((f - j r : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr (hjf r))
    rw [hcast]
    apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg (by norm_num))
    exact_mod_cast sub_le_sub_left (hij r) f
  have hpoint (r : (S.wordRatioLaw n).support) :
      γ * H r ≤ γ * e * D + C r - T r + Real.log 2 + γ * D * (if r ∈ G then 0 else 1) := by
    by_cases hr : r ∈ G
    · obtain ⟨hm, hlo, hhi⟩ := hgood r hr
      have h := hgain (f - j r).toNat hm (S.ratioDilation n r) (j r)
        (S.ratioTranslationProbability n r) (S.ratioTranslationProbability_hasBoundedSupport n r)
        hlo hhi rfl
      simp only [hlevel] at h
      change γ * H r ≤ γ * e * (((f - j r).toNat : ℝ) * Real.log 2) + C r - T r + Real.log 2 at h
      have hb := mul_le_mul_of_nonneg_left (hdepth r) (mul_nonneg hγ.le he.le)
      simp only [hr, ite_true, mul_zero, add_zero]
      linarith
    · have h := average_component_entropy_trivial_bound
        (S.ratioTranslationProbability n r) (S.ratioScaledProbability μ n r)
        (S.ratioTranslationProbability_hasBoundedSupport n r)
        (S.ratioScaledProbability_hasBoundedSupport μ (S.hasBoundedSupport hμ) n r)
        (j r) (f - j r).toNat hγ.le
      simp only [hlevel] at h
      change γ * H r ≤ γ * (((f - j r).toNat : ℝ) * Real.log 2) + C r - T r + Real.log 2 at h
      have hb := mul_le_mul_of_nonneg_left (hdepth r) hγ.le
      simp only [hr, ite_false, mul_one]
      nlinarith [mul_nonneg (mul_nonneg hγ.le he.le) hD]
  have hav := Finset.sum_le_sum (s := Finset.univ) (fun r _ ↦
    mul_le_mul_of_nonneg_left (hpoint r) (show 0 ≤ (p r).toReal from ENNReal.toReal_nonneg))
  have hleft : (∑ r, (p r).toReal * (γ * H r)) = γ * S.averageVariableRatioTranslationEntropy n j f := by
    unfold averageVariableRatioTranslationEntropy
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    simp only [p, supportLaw_apply, H]
    ring
  have hbad : (∑ r, (p r).toReal * (γ * D * (if r ∈ G then 0 else 1))) =
      γ * D * S.ratioClassBadMass n G := by
    unfold ratioClassBadMass
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    simp only [p, supportLaw_apply]
    split_ifs
    · simp only [mul_zero]
    · simp only [mul_one]
      ring
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib] at hav
  rw [← Finset.sum_mul, sum_pmf_toReal, one_mul, ← Finset.sum_mul, sum_pmf_toReal, one_mul] at hav
  rw [hleft, hbad] at hav
  change γ * S.averageVariableRatioTranslationEntropy n j f ≤
    γ * e * D + S.averageVariableRatioConvolutionEntropy μ (S.hasBoundedSupport hμ) n j f -
      S.averageRatioScaledEntropy μ (S.hasBoundedSupport hμ) n f + Real.log 2 +
        γ * D * S.ratioClassBadMass n G at hav
  have hc := S.averageVariableRatioConvolutionEntropy_le μ hμ n j hif hij hjf
  dsimp [D] at hav
  nlinarith

end ExactOverlaps.SelfSimilar.System
