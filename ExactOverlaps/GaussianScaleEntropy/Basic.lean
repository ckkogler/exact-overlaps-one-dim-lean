/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.ScaleEntropy.Averaged
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Countable entropy at a physical scale

Cell entropy is first defined as a nonnegative extended-real sum. Its real
form is used only after finiteness is proved. These definitions agree
exactly with the existing entropy for bounded-support laws; they also
allow Gaussian and other unbounded laws with finite second moment.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace ExactOverlaps.GaussianScaleEntropy

def cellTerm (μ : ProbabilityMeasure ℝ) (r t : ℝ) (k : ℤ) : ℝ :=
  Real.negMulLog (ScaleEntropy.law μ r t k).toReal

lemma cellTerm_nonneg (μ : ProbabilityMeasure ℝ) (r t : ℝ) (k : ℤ) :
    0 ≤ cellTerm μ r t k :=
  Real.negMulLog_nonneg ENNReal.toReal_nonneg
    (by simpa using (ENNReal.toReal_mono ENNReal.one_ne_top
      ((ScaleEntropy.law μ r t).coe_le_one k)))

lemma cellTerm_le_one (μ : ProbabilityMeasure ℝ) (r t : ℝ) (k : ℤ) :
    cellTerm μ r t k ≤ 1 := by
  exact (Real.negMulLog_le_one_sub_self ENNReal.toReal_nonneg).trans
    (sub_le_self _ ENNReal.toReal_nonneg)

def cellEntropy (μ : ProbabilityMeasure ℝ) (r t : ℝ) : ℝ≥0∞ :=
  ∑' k : ℤ, ENNReal.ofReal (cellTerm μ r t k)

def shiftedEntropy (μ : ProbabilityMeasure ℝ) (r t : ℝ) : ℝ :=
  (cellEntropy μ r t).toReal

def entropy (μ : ProbabilityMeasure ℝ) (r : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..r, shiftedEntropy μ r t) / r

def entropyBetween (μ : ProbabilityMeasure ℝ) (r R : ℝ) : ℝ :=
  entropy μ r - entropy μ R

lemma cellEntropy_ne_top_of_summable (μ : ProbabilityMeasure ℝ) (r t : ℝ)
    (h : Summable (cellTerm μ r t)) : cellEntropy μ r t ≠ ∞ :=
  h.tsum_ofReal_ne_top

lemma shiftedEntropy_eq_tsum (μ : ProbabilityMeasure ℝ) (r t : ℝ)
    (h : Summable (cellTerm μ r t)) :
    shiftedEntropy μ r t = ∑' k : ℤ, cellTerm μ r t k := by
  rw [shiftedEntropy, cellEntropy, ← ENNReal.ofReal_tsum_of_nonneg
    (cellTerm_nonneg μ r t) h, ENNReal.toReal_ofReal]
  exact tsum_nonneg (cellTerm_nonneg μ r t)

lemma summable_cellTerm_of_bounded (μ : ProbabilityMeasure ℝ)
    (hμ : Entropy.HasBoundedSupport μ) {r : ℝ} (hr : 0 < r) (t : ℝ) :
    Summable (cellTerm μ r t) := by
  apply summable_of_ne_finset_zero (s := (ScaleEntropy.law_support_finite μ hμ hr t).toFinset)
  intro k hk
  have hz : ScaleEntropy.law μ r t k = 0 := by simpa using hk
  simp [cellTerm, hz]

lemma shiftedEntropy_eq_bounded (μ : ProbabilityMeasure ℝ)
    (hμ : Entropy.HasBoundedSupport μ) {r : ℝ} (hr : 0 < r) (t : ℝ) :
    shiftedEntropy μ r t = ScaleEntropy.shiftedEntropy μ hμ r hr t := by
  rw [shiftedEntropy_eq_tsum μ r t (summable_cellTerm_of_bounded μ hμ hr t),
    ScaleEntropy.shiftedEntropy_eq_tsum]
  rfl

lemma entropy_eq_bounded (μ : ProbabilityMeasure ℝ)
    (hμ : Entropy.HasBoundedSupport μ) {r : ℝ} (hr : 0 < r) :
    entropy μ r = ScaleEntropy.entropy μ hμ r hr := by
  unfold entropy ScaleEntropy.entropy
  simp only [shiftedEntropy_eq_bounded μ hμ hr]

lemma entropyBetween_eq_bounded (μ : ProbabilityMeasure ℝ)
    (hμ : Entropy.HasBoundedSupport μ) {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    entropyBetween μ r R = ScaleEntropy.entropyBetween μ hμ r hr R hR := by
  simp only [entropyBetween, ScaleEntropy.entropyBetween, entropy_eq_bounded μ hμ hr,
    entropy_eq_bounded μ hμ hR]

@[fun_prop] lemma measurable_cellTerm (μ : ProbabilityMeasure ℝ) (r : ℝ) (k : ℤ) :
    Measurable (fun t ↦ cellTerm μ r t k) :=
  Real.continuous_negMulLog.measurable.comp
    (ScaleEntropy.measurable_law_apply μ r k).ennreal_toReal

@[fun_prop] lemma measurable_cellEntropy (μ : ProbabilityMeasure ℝ) (r : ℝ) :
    Measurable (cellEntropy μ r) :=
  Measurable.tsum (fun k ↦ (measurable_cellTerm μ r k).ennreal_ofReal)

@[fun_prop] lemma measurable_shiftedEntropy (μ : ProbabilityMeasure ℝ) (r : ℝ) :
    Measurable (shiftedEntropy μ r) :=
  (measurable_cellEntropy μ r).ennreal_toReal

lemma shiftedEntropy_nonneg (μ : ProbabilityMeasure ℝ) (r t : ℝ) :
    0 ≤ shiftedEntropy μ r t := ENNReal.toReal_nonneg

end ExactOverlaps.GaussianScaleEntropy
