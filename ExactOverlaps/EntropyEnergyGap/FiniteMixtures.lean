module

public import ExactOverlaps.VarianceEnergy.Concavity
public import ExactOverlaps.Entropy.ConditionalConcavity

/-!
# Variance energy below a scale under finite mixtures

The checked binary concavity inequality iterates over any finite family
of finite measures and finite nonnegative weights. Actual PMF binding and
conditioning are then identified with those mixtures as measures.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal Classical
open ExactOverlaps.Entropy ExactOverlaps.VarianceEnergy

namespace ExactOverlaps.EntropyEnergyGap

lemma energyBelow_finset_mixture_le {ι : Type*} (s : Finset ι)
    (w : ι → ℝ≥0∞) (hw : ∀ i, w i ≠ ∞)
    (μ : ι → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] (R : ℝ) :
    (∑ i ∈ s, w i * energyBelow (μ i) R) ≤ energyBelow (∑ i ∈ s, w i • μ i) R := by
  let : ∀ i, IsFiniteMeasure (w i • μ i) := fun i ↦ Measure.smul_finite (μ i) (hw i)
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact zero_le
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    apply (add_le_add le_rfl ih).trans
    simpa only [one_mul, one_smul] using
      energyBelow_mixture_le (w a) 1 (μ a) (∑ i ∈ s, w i • μ i) R

lemma bind_toMeasure_eq_sum {ι : Type*} [Fintype ι] (p : PMF ι) (q : ι → PMF ℝ) :
    (p.bind q).toMeasure = ∑ i, p i • (q i).toMeasure := by
  ext s hs : 1
  rw [PMF.toMeasure_bind_apply _ _ _ hs, tsum_fintype, Measure.finsetSum_apply Finset.univ (fun i ↦ p i • (q i).toMeasure) s]
  simp only [Measure.smul_apply, smul_eq_mul]

theorem energyBelow_bind_le {ι : Type*} [Fintype ι] (p : PMF ι) (q : ι → PMF ℝ) (R : ℝ) :
    (∑ i, p i * energyBelow (q i).toMeasure R) ≤ energyBelow (p.bind q).toMeasure R := by
  rw [bind_toMeasure_eq_sum]
  exact energyBelow_finset_mixture_le Finset.univ p p.apply_ne_top (fun i ↦ (q i).toMeasure) R

theorem energyBelow_conditional_le {β : Type*} (p : PMF ℝ) (hp : p.support.Finite)
    (f : ℝ → β) (R : ℝ) :
    (letI : Fintype (p.map f).support :=
      (show (p.map f).support.Finite from by simpa using hp.image f).fintype
    ∑ b : (p.map f).support, (p.map f) b * energyBelow (conditionalPMF p f b).toMeasure R) ≤
      energyBelow p.toMeasure R := by
  let : Fintype (p.map f).support :=
    (show (p.map f).support.Finite from by simpa using hp.image f).fintype
  have h := energyBelow_bind_le (supportLaw (p.map f)) (conditionalPMF p f) R
  rw [bind_conditionalPMF p hp f] at h
  exact h

end ExactOverlaps.EntropyEnergyGap
