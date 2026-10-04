module

public import ExactOverlaps.ScaleEntropy.Concavity
public import ExactOverlaps.EntropyEnergyGap.DigitArray
public import ExactOverlaps.EntropyEnergyGap.ConditionalEnergy

/-! Genuine finite-mixture bounds for averaged entropy and variance energy. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators

namespace ExactOverlaps.ScaleEntropy

open Entropy

theorem entropy_mixture_le {ι : Type*} [Fintype ι] (p : PMF ι)
    (ν : ι → ProbabilityMeasure ℝ) (hν : ∀ i, HasBoundedSupport (ν i))
    (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ)
    (hmix : (μ : Measure ℝ) = ∑ i, p i • (ν i : Measure ℝ))
    (r : ℝ) (hr : 0 < r) :
    (∑ i, (p i).toReal * entropy (ν i) (hν i) r hr) ≤ entropy μ hμ r hr := by
  have hb (t : ℝ) : (∑ i, (p i).toReal * shiftedEntropy (ν i) (hν i) r hr t) ≤
      shiftedEntropy μ hμ r hr t := by
    have h := average_finiteEntropy_le_bind p (fun i ↦ law (ν i) r t)
      (fun i ↦ law_support_finite (ν i) (hν i) hr t)
    simpa only [← law_eq_bind_of_measure_eq p ν μ hmix r t, shiftedEntropy] using h
  have hi (i : ι) := intervalIntegrable_shiftedEntropy (ν i) (hν i) r hr 0 r
  have hsum : IntervalIntegrable (fun t ↦ ∑ i, (p i).toReal *
      shiftedEntropy (ν i) (hν i) r hr t) volume 0 r := by
    convert (IntervalIntegrable.sum (s := Finset.univ)
      (fun i _ ↦ (hi i).const_mul (p i).toReal)) using 1
    funext t
    simp only [Finset.sum_apply]
  have h := intervalIntegral.integral_mono_on hr.le hsum
    (intervalIntegrable_shiftedEntropy μ hμ r hr 0 r) (fun t _ ↦ hb t)
  rw [intervalIntegral.integral_finsetSum (fun i _ ↦ (hi i).const_mul (p i).toReal)] at h
  simp_rw [intervalIntegral.integral_const_mul] at h
  have hd := div_le_div_of_nonneg_right h hr.le
  simpa only [entropy, Finset.sum_div, mul_div_assoc] using hd

end ExactOverlaps.ScaleEntropy

namespace ExactOverlaps.SelfSimilar

open Entropy EntropyEnergyGap VarianceEnergy

theorem conditional_map_bind {α β : Type*} (p : PMF α) (hp : p.support.Finite)
    (f : α → β) (B : α → ℝ) :
    (supportLaw (p.map f)).bind (fun b ↦ (conditionalPMF p f b).map B) = p.map B := by
  rw [← PMF.map_bind, bind_conditionalPMF p hp f]

theorem average_mapped_conditional_scaleEntropy_le {α β : Type*}
    (p : PMF α) (hp : p.support.Finite) (f : α → β) (B : α → ℝ)
    (r : ℝ) (hr : 0 < r) :
    (letI : Fintype (p.map f).support := (show (p.map f).support.Finite from by
      simpa using hp.image f).fintype
    ∑ b : (p.map f).support, ((p.map f) b).toReal *
      ScaleEntropy.entropy (finiteLawProbability ((conditionalPMF p f b).map B))
        (finiteLawProbability_bounded _ (by simpa using (conditionalPMF_support_finite p hp f b).image B))
        r hr) ≤
      ScaleEntropy.entropy (finiteLawProbability (p.map B))
        (finiteLawProbability_bounded _ (by simpa using hp.image B)) r hr := by
  let : Fintype (p.map f).support := (show (p.map f).support.Finite from by
    simpa using hp.image f).fintype
  have hmix : (finiteLawProbability (p.map B) : Measure ℝ) =
      ∑ b : (p.map f).support, (supportLaw (p.map f)) b •
        (finiteLawProbability ((conditionalPMF p f b).map B) : Measure ℝ) := by
    change (p.map B).toMeasure = _
    rw [← conditional_map_bind p hp f B, bind_toMeasure_eq_sum]
    rfl
  exact ScaleEntropy.entropy_mixture_le (supportLaw (p.map f))
    (fun b ↦ finiteLawProbability ((conditionalPMF p f b).map B))
    (fun b ↦ finiteLawProbability_bounded _
      (by simpa using (conditionalPMF_support_finite p hp f b).image B))
    (finiteLawProbability (p.map B))
    (finiteLawProbability_bounded _ (by simpa using hp.image B)) hmix r hr

theorem average_mapped_conditional_energyBelow_le {α β : Type*}
    (p : PMF α) (hp : p.support.Finite) (f : α → β) (B : α → ℝ) (r : ℝ) :
    (letI : Fintype (p.map f).support := (show (p.map f).support.Finite from by
      simpa using hp.image f).fintype
    ∑ b : (p.map f).support, ((p.map f) b).toReal *
      (energyBelow ((conditionalPMF p f b).map B).toMeasure r).toReal) ≤
      (energyBelow (p.map B).toMeasure r).toReal := by
  let : Fintype (p.map f).support := (show (p.map f).support.Finite from by
    simpa using hp.image f).fintype
  have h := energyBelow_bind_le (supportLaw (p.map f))
    (fun b ↦ (conditionalPMF p f b).map B) r
  rw [conditional_map_bind p hp f B] at h
  have h' := ENNReal.toReal_mono
    (finiteLaw_energyBelow_ne_top (p.map B) (by simpa using hp.image B) r) h
  rw [ENNReal.toReal_sum (fun b _ ↦ ENNReal.mul_ne_top
    ((supportLaw (p.map f)).apply_ne_top b)
    (finiteLaw_energyBelow_ne_top _
      (by simpa using (conditionalPMF_support_finite p hp f b).image B) r))] at h'
  simpa only [ENNReal.toReal_mul, supportLaw_apply] using h'

end ExactOverlaps.SelfSimilar
