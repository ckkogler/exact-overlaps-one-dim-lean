module

public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# Absolute dispersion of finite laws

The dispersion of a real statistic is the mean absolute distance between two
independent samples from its law. The finite double-sum definition keeps its
probabilistic meaning explicit. Subadditivity applies even to dependent
statistics on a common probability space, as needed after conditioning on a
tuple of cells in the entropy-loss argument.
-/

@[expose] public section

open scoped BigOperators ENNReal
open MeasureTheory

namespace ExactOverlaps.FiniteLaw

/-- Mean absolute distance between independent samples of a real statistic. -/
noncomputable def dispersion {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (f : α → ℝ) : ℝ :=
  ∑ a ∈ hp.toFinset, (p a).toReal *
    ∑ b ∈ hp.toFinset, (p b).toReal * |f a - f b|

lemma dispersion_nonneg {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (f : α → ℝ) : 0 ≤ dispersion p hp f := by
  unfold dispersion
  exact Finset.sum_nonneg (fun a _ ↦ mul_nonneg ENNReal.toReal_nonneg
    (Finset.sum_nonneg (fun b _ ↦ mul_nonneg ENNReal.toReal_nonneg (abs_nonneg _))))

lemma dispersion_congr {α : Type*} (p : PMF α) (hp : p.support.Finite)
    {f g : α → ℝ} (hfg : ∀ a ∈ p.support, f a = g a) :
    dispersion p hp f = dispersion p hp g := by
  unfold dispersion
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  apply Finset.sum_congr rfl
  intro b hb
  rw [hfg a (by simpa using ha), hfg b (by simpa using hb)]

@[simp] lemma dispersion_const {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (c : ℝ) : dispersion p hp (fun _ ↦ c) = 0 := by
  simp [dispersion]

@[simp] lemma dispersion_add_const {α : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → ℝ) (c : ℝ) :
    dispersion p hp (fun a ↦ f a + c) = dispersion p hp f := by
  simp only [dispersion, add_sub_add_right_eq_sub]

lemma dispersion_mul_const {α : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → ℝ) (c : ℝ) :
    dispersion p hp (fun a ↦ c * f a) = |c| * dispersion p hp f := by
  simp only [dispersion, ← mul_sub, abs_mul]
  simp_rw [mul_left_comm (p _).toReal |c|, ← Finset.mul_sum]
  simp_rw [mul_left_comm (p _).toReal |c|]
  rw [← Finset.mul_sum]

lemma dispersion_affine {α : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → ℝ) (a b : ℝ) :
    dispersion p hp (fun x ↦ a * f x + b) = |a| * dispersion p hp f := by
  rw [dispersion_add_const, dispersion_mul_const]

@[simp] lemma dispersion_neg {α : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → ℝ) :
    dispersion p hp (fun a ↦ -f a) = dispersion p hp f := by
  simpa using dispersion_mul_const p hp f (-1)

lemma dispersion_add_le {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (f g : α → ℝ) :
    dispersion p hp (fun a ↦ f a + g a) ≤ dispersion p hp f + dispersion p hp g := by
  unfold dispersion
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  rw [← mul_add, ← Finset.sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  apply Finset.sum_le_sum
  intro b _
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  have he : f a + g a - (f b + g b) = (f a - f b) + (g a - g b) := by ring
  rw [he]
  exact abs_add_le _ _

lemma dispersion_sub_le {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (f g : α → ℝ) :
    dispersion p hp (fun a ↦ f a - g a) ≤ dispersion p hp f + dispersion p hp g := by
  simpa only [sub_eq_add_neg, dispersion_neg] using
    dispersion_add_le p hp f (fun a ↦ -g a)

/-- Dispersion is subadditive for any finite family of real statistics. -/
lemma dispersion_sum_le {α ι : Type*} (p : PMF α) (hp : p.support.Finite)
    (s : Finset ι) (f : ι → α → ℝ) :
    dispersion p hp (fun a ↦ ∑ i ∈ s, f i a) ≤ ∑ i ∈ s, dispersion p hp (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (dispersion_add_le p hp (f i) (fun a ↦ ∑ j ∈ s, f j a)).trans
      (add_le_add le_rfl ih)

lemma sum_support_mass {α : Type*} (p : PMF α) (hp : p.support.Finite) :
    ∑ a ∈ hp.toFinset, (p a).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun a _ ↦ p.apply_ne_top a)]
  have hs : ∑ a ∈ hp.toFinset, p a = 1 := by
    rw [← p.tsum_coe]
    exact (tsum_eq_sum (fun a ha ↦ by simpa using ha)).symm
  rw [hs, ENNReal.toReal_one]

/-- A bound on the diameter of the statistic bounds its dispersion. -/
lemma dispersion_le_of_diameter {α : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → ℝ) {D : ℝ}
    (hD : ∀ a ∈ p.support, ∀ b ∈ p.support, |f a - f b| ≤ D) :
    dispersion p hp f ≤ D := by
  calc
    dispersion p hp f ≤
        ∑ a ∈ hp.toFinset, (p a).toReal * ∑ b ∈ hp.toFinset, (p b).toReal * D := by
      apply Finset.sum_le_sum
      intro a ha
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      apply Finset.sum_le_sum
      intro b hb
      exact mul_le_mul_of_nonneg_left
        (hD a (by simpa using ha) b (by simpa using hb)) ENNReal.toReal_nonneg
    _ = D := by
      simp only [← Finset.sum_mul, sum_support_mass, one_mul]

/-- The finite formula is the actual expected distance between independent samples. -/
theorem dispersion_eq_iterated_integral {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : PMF α) (hp : p.support.Finite)
    (f : α → ℝ) :
    dispersion p hp f = ∫ a, ∫ b, |f a - f b| ∂p.toMeasure ∂p.toMeasure := by
  have hint (g : α → ℝ) : MeasureTheory.Integrable g p.toMeasure := by
    have h : MeasureTheory.IntegrableOn g p.support p.toMeasure :=
      MeasureTheory.IntegrableOn.of_finite hp
    rwa [MeasureTheory.IntegrableOn, PMF.restrict_toMeasure_support] at h
  have hi (g : α → ℝ) :
      (∫ a, g a ∂p.toMeasure) = ∑ a ∈ hp.toFinset, (p a).toReal * g a := by
    rw [PMF.integral_eq_tsum p g (hint g)]
    apply tsum_eq_sum
    intro a ha
    have hz : p a = 0 := by simpa using ha
    simp [hz]
  simp_rw [hi]
  rfl

end ExactOverlaps.FiniteLaw
