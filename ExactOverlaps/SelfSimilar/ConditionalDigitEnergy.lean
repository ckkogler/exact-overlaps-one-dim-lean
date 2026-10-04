module

public import ExactOverlaps.SelfSimilar.ConditionalMapEnergy
public import ExactOverlaps.SelfSimilar.EntropyComparison

/-!
Proposition 3.3 averaged over an actual finite observation. On every fiber
the coefficients are fixed; the encoded digit law may retain arbitrary
dependence, as permitted by the proved finite-array energy estimate.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators Classical

namespace ExactOverlaps.SelfSimilar

open Entropy EntropyEnergyGap VarianceEnergy FiniteProbability

theorem conditional_digit_energy_gap {Ω α β J : Type*} [Fintype α] [Fintype J]
    (p : PMF Ω) (hp : p.support.Finite) (f : Ω → β) (B : Ω → ℝ)
    (encode : Ω → J → α) (v : J → α → ℝ) (a : β → J → ℝ) (a₀ : α)
    (hB : ∀ x ∈ p.support, B x = digitValueSum v (a (f x)) (encode x))
    (m : ℕ) (hm : 0 < m) {r : ℝ} (hr : 0 < r) (b : (p.map f).support) :
    1 / (30 * m) *
      (finiteEntropy ((conditionalPMF p f b).map B)
          (by simpa using (conditionalPMF_support_finite p hp f b).image B) -
        ScaleEntropy.entropy (finiteLawProbability ((conditionalPMF p f b).map B))
          (finiteLawProbability_bounded _
            (by simpa using (conditionalPMF_support_finite p hp f b).image B)) r hr -
        (Fintype.card J : ℝ) * (Fintype.card α - 1 : ℕ) * Real.log (m + 1 : ℝ) / m) - 1 / 2 ≤
      (energyBelow ((conditionalPMF p f b).map B).toMeasure r).toReal := by
  let q := conditionalPMF p f b
  have hq := conditionalPMF_support_finite p hp f b
  have he : (q.map encode).map (digitValueSum v (a b)) = q.map B := by
    rw [PMF.map_comp]
    apply map_congr_on_support
    intro x hx
    have hx' := hx
    change x ∈ (conditionalPMF p f b).support at hx'
    rw [conditionalPMF_support] at hx'
    have hb := hB x hx'.2
    rw [hx'.1] at hb
    exact hb.symm
  have h := digit_array_energy_gap (finiteLawProbability (q.map B))
    (finiteLawProbability_bounded _ (by simpa using hq.image B)) v (a b) a₀ (q.map encode)
    (by change (q.map B).toMeasure = _; rw [he]) m hm hr
  have hμ : (finiteLawProbability (q.map B) : Measure ℝ) = (q.map B).toMeasure := rfl
  simpa only [he, hμ, q] using h

theorem mean_conditional_digit_energy_gap {Ω α β J : Type*} [Fintype α] [Fintype J]
    (p : PMF Ω) (hp : p.support.Finite) (f : Ω → β) (B : Ω → ℝ)
    (encode : Ω → J → α) (v : J → α → ℝ) (a : β → J → ℝ) (a₀ : α)
    (hB : ∀ x ∈ p.support, B x = digitValueSum v (a (f x)) (encode x))
    (m : ℕ) (hm : 0 < m) {r : ℝ} (hr : 0 < r) :
    1 / (30 * m) *
      (finiteEntropy (p.map B) (by simpa using hp.image B) -
        finiteEntropy (p.map f) (by simpa using hp.image f) -
        ScaleEntropy.entropy (finiteLawProbability (p.map B))
          (finiteLawProbability_bounded _ (by simpa using hp.image B)) r hr -
        (Fintype.card J : ℝ) * (Fintype.card α - 1 : ℕ) * Real.log (m + 1 : ℝ) / m) - 1 / 2 ≤
      meanConditionalMapEnergy p hp f B r := by
  let : Fintype (p.map f).support := (show (p.map f).support.Finite from by
    simpa using hp.image f).fintype
  let w (b : (p.map f).support) := ((p.map f) b).toReal
  let H (b : (p.map f).support) := finiteEntropy ((conditionalPMF p f b).map B)
    (by simpa using (conditionalPMF_support_finite p hp f b).image B)
  let E (b : (p.map f).support) := ScaleEntropy.entropy
    (finiteLawProbability ((conditionalPMF p f b).map B))
    (finiteLawProbability_bounded _ (by simpa using (conditionalPMF_support_finite p hp f b).image B)) r hr
  let A : ℝ := 1 / (30 * m)
  let c : ℝ := (Fintype.card J : ℝ) * (Fintype.card α - 1 : ℕ) * Real.log (m + 1 : ℝ) / m
  have hw : (∑ b : (p.map f).support, w b) = 1 := sum_pmf_toReal (supportLaw (p.map f))
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun b _ ↦
    mul_le_mul_of_nonneg_left
      (conditional_digit_energy_gap p hp f B encode v a a₀ hB m hm hr b)
      (show 0 ≤ w b from ENNReal.toReal_nonneg))
  have hcalc : (∑ b : (p.map f).support, w b * (A * (H b - E b - c) - 1 / 2)) =
      A * ((∑ b, w b * H b) - (∑ b, w b * E b) - c) - 1 / 2 := by
    calc
      _ = ∑ b : (p.map f).support,
          (A * (w b * H b) - A * (w b * E b) - w b * (A * c + 1 / 2)) := by
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = _ := by
        simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hw, one_mul]
        ring
  change (∑ b : (p.map f).support, w b * (A * (H b - E b - c) - 1 / 2)) ≤ _ at hsum
  rw [hcalc] at hsum
  have hH := entropy_sub_le_conditional_statistic p hp f B
  have hE := average_mapped_conditional_scaleEntropy_le p hp f B r hr
  change finiteEntropy (p.map B) _ - finiteEntropy (p.map f) _ ≤ ∑ b, w b * H b at hH
  change (∑ b, w b * E b) ≤ ScaleEntropy.entropy (finiteLawProbability (p.map B)) _ r hr at hE
  change A * (_ - _ - _ - c) - 1 / 2 ≤ _
  rw [meanConditionalMapEnergy, meanFiberFunctional_eq_sum]
  apply le_trans _ hsum
  apply sub_le_sub_right
  apply mul_le_mul_of_nonneg_left _ (show 0 ≤ A by dsimp [A]; positivity)
  linarith

end ExactOverlaps.SelfSimilar
