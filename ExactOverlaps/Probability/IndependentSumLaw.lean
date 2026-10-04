module

public import ExactOverlaps.Probability.FiniteLawMeasureProduct
public import ExactOverlaps.Entropy.FiniteProductLaw
public import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# Standard independent random variables have the finite tuple sum law

The genuine PMF sum law has the product characteristic function. Standard
measure-theoretic independence gives the same characteristic function on
any probability space, so the two sum laws agree as Borel measures.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

namespace ExactOverlaps.Entropy

lemma tupleLaw_sum_succ (m : ℕ) (p : Fin (m + 1) → PMF ℝ) :
    (tupleLaw (m + 1) p).map (tupleSum id (m + 1)) =
      discreteConvolution (p 0) ((tupleLaw m (fun i ↦ p i.succ)).map (tupleSum id m)) := by
  rw [discreteConvolution, ← independentPair_map_right, PMF.map_comp]
  rfl

lemma charFun_tupleLaw_sum (m : ℕ) (p : Fin m → PMF ℝ)
    (hp : ∀ i, (p i).support.Finite) (t : ℝ) :
    charFun ((tupleLaw m p).map (tupleSum id m)).toMeasure t =
      ∏ i, charFun (p i).toMeasure t := by
  induction m with
  | zero =>
    change charFun ((PMF.pure PUnit.unit).map (fun _ ↦ (0 : ℝ))).toMeasure t = _
    rw [PMF.pure_map, PMF.toMeasure_pure]
    simp [charFun_dirac]
  | succ m ih =>
    rw [tupleLaw_sum_succ, finite_discreteConvolution_toMeasure (p 0) _ (hp 0)
      (by simpa using (tupleLaw_support_finite m (fun i ↦ p i.succ) (fun i ↦ hp i.succ)).image (tupleSum id m)), charFun_conv, Fin.prod_univ_succ]
    rw [ih (fun i ↦ p i.succ) (fun i ↦ hp i.succ)]

theorem independent_sum_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : ℕ) (X : Fin m → Ω → ℝ)
    (hXm : ∀ i, AEMeasurable (X i) μ) (hXi : iIndepFun X μ)
    (p : Fin m → PMF ℝ) (hp : ∀ i, (p i).support.Finite)
    (hLaw : ∀ i, μ.map (X i) = (p i).toMeasure) :
    μ.map (fun ω ↦ ∑ i, X i ω) = ((tupleLaw m p).map (tupleSum id m)).toMeasure := by
  apply Measure.ext_of_charFun
  rw [hXi.charFun_map_fun_sum_eq_prod hXm]
  funext t
  simp only [Finset.prod_apply, hLaw, charFun_tupleLaw_sum m p hp t]

end ExactOverlaps.Entropy
