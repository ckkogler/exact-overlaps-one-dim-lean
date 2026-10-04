module

public import ExactOverlaps.Probability.FiniteCDF
public import ExactOverlaps.Probability.FiniteIntegration
public import ExactOverlaps.Probability.Dispersion
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The independent-sample distance tail

The complement of a shifted cumulative mass is the probability that an
independent sample exceeds the observed sample by the shift. Integrating
this tail over positive shifts gives half the absolute dispersion.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical

namespace ExactOverlaps.FiniteProbability

noncomputable def distanceTail {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (x : α → ℝ) (u : ℝ) : ℝ :=
  expectation p hp (fun a ↦ expectation p hp (fun b ↦ if x a + u < x b then 1 else 0))

lemma distanceTail_nonneg {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (x : α → ℝ) (u : ℝ) : 0 ≤ distanceTail p hp x u := by
  apply expectation_nonneg p hp
  intro a _
  apply expectation_nonneg p hp
  intro b _
  split_ifs <;> norm_num

lemma distanceTail_eq_cumulative_complement {α : Type*} (p : PMF α)
    (hp : p.support.Finite) (x : α → ℝ) (u : ℝ) :
    distanceTail p hp x u = expectation p hp (fun a ↦ 1 - cumulativeMass p hp x (x a + u)) := by
  simp_rw [one_sub_cumulativeMass]
  rfl

lemma integrableOn_positive_tail_indicator (d : ℝ) :
    IntegrableOn (fun u : ℝ ↦ if u < d then (1 : ℝ) else 0) (Ioi 0) := by
  have hf : Integrable ((Ioo (0 : ℝ) d).indicator (fun _ ↦ (1 : ℝ))) volume := by
    apply (integrable_indicator_iff measurableSet_Ioo).mpr
    have hs : volume (Ioo (0 : ℝ) d) ≠ ∞ := by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_ne_top
    exact integrableOn_const hs
  apply hf.restrict.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  simp [Set.indicator, show 0 < u from hu]

lemma integral_positive_tail_indicator (d : ℝ) :
    (∫ u : ℝ in Ioi 0, if u < d then (1 : ℝ) else 0) = max d 0 := by
  have he : (fun u : ℝ ↦ if u < d then (1 : ℝ) else 0) =
      (Iio d).indicator (fun _ ↦ (1 : ℝ)) := by
    funext u
    simp [Set.indicator]
  rw [he, integral_indicator_const _ measurableSet_Iio]
  simp only [Measure.real, Measure.restrict_apply measurableSet_Iio, smul_eq_mul, mul_one]
  have hs : Iio d ∩ Ioi (0 : ℝ) = Ioo 0 d := by ext u; simp [and_comm]
  rw [hs, Real.volume_Ioo, sub_zero]
  by_cases hd : 0 ≤ d
  · rw [ENNReal.toReal_ofReal hd, max_eq_left hd]
  · rw [ENNReal.ofReal_eq_zero.mpr (le_of_not_ge hd), ENNReal.toReal_zero,
      max_eq_right (le_of_not_ge hd)]

lemma integrableOn_distanceTail {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (x : α → ℝ) : IntegrableOn (distanceTail p hp x) (Ioi 0) := by
  apply integrable_expectation p hp
  intro a _
  apply integrable_expectation p hp
  intro b _
  have he : (fun u : ℝ ↦ if x a + u < x b then (1 : ℝ) else 0) =
      (fun u : ℝ ↦ if u < x b - x a then (1 : ℝ) else 0) := by
    funext u
    simp only [show x a + u < x b ↔ u < x b - x a by constructor <;> intro h <;> linarith]
  rw [he]
  exact integrableOn_positive_tail_indicator _

lemma integral_distanceTail_eq_positive_part {α : Type*} (p : PMF α)
    (hp : p.support.Finite) (x : α → ℝ) :
    (∫ u : ℝ in Ioi 0, distanceTail p hp x u) =
      expectation p hp (fun a ↦ expectation p hp (fun b ↦ max (x b - x a) 0)) := by
  have hi (a b : α) : IntegrableOn (fun u : ℝ ↦ if x a + u < x b then (1 : ℝ) else 0)
      (Ioi 0) := by
    convert integrableOn_positive_tail_indicator (x b - x a) using 1
    funext u
    simp only [show x a + u < x b ↔ u < x b - x a by constructor <;> intro h <;> linarith]
  unfold distanceTail
  rw [integral_expectation p hp _ (fun a _ ↦ integrable_expectation p hp _ (fun b _ ↦ hi a b))]
  congr 1
  funext a
  rw [integral_expectation p hp _ (fun b _ ↦ hi a b)]
  congr 1
  funext b
  have he : (fun u : ℝ ↦ if x a + u < x b then (1 : ℝ) else 0) =
      (fun u : ℝ ↦ if u < x b - x a then (1 : ℝ) else 0) := by
    funext u
    simp only [show x a + u < x b ↔ u < x b - x a by constructor <;> intro h <;> linarith]
  rw [he, integral_positive_tail_indicator]

lemma integral_distanceTail {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (x : α → ℝ) :
    (∫ u : ℝ in Ioi 0, distanceTail p hp x u) = FiniteLaw.dispersion p hp x / 2 := by
  rw [integral_distanceTail_eq_positive_part]
  have hsymm : expectation p hp (fun a ↦ expectation p hp (fun b ↦ max (x a - x b) 0)) =
      expectation p hp (fun a ↦ expectation p hp (fun b ↦ max (x b - x a) 0)) := by
    unfold expectation
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  have he (a b : α) : |x a - x b| = max (x a - x b) 0 + max (x b - x a) 0 := by
    rw [abs_eq_max_neg]
    simp only [max_def]
    split_ifs <;> linarith
  have hd : FiniteLaw.dispersion p hp x =
      2 * expectation p hp (fun a ↦ expectation p hp (fun b ↦ max (x b - x a) 0)) := by
    change expectation p hp (fun a ↦ expectation p hp (fun b ↦ |x a - x b|)) = _
    simp_rw [he, expectation_add]
    rw [hsymm]
    ring
  rw [hd]
  ring

end ExactOverlaps.FiniteProbability
