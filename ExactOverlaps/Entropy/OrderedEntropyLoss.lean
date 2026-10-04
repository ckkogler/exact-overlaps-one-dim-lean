module

public import ExactOverlaps.Entropy.GridRevealRate
public import ExactOverlaps.Entropy.FiniteProductEntropy
public import ExactOverlaps.Probability.OrderedPoissonReal

/-!
# Entropy loss for independent laws on a common ordered grid

Integrating the true reveal rate gives the entropy lost under addition.
The rate estimate and the finite real Poisson-energy bound give the constant
twenty-seven, and hence the stated constant thirty.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators Classical
open ExactOverlaps.Poisson

namespace ExactOverlaps.Entropy

theorem ordered_entropy_loss_le_twenty_seven {m n : ℕ}
    (p : Fin m → PMF (Fin (n + 1))) (hp : ∀ i, (p i).support.Finite) (x : ℕ → ℝ)
    (hx : StrictMono (fun k : Fin (n + 1) ↦ x k.val)) :
    (∑ i, finiteEntropy (p i) (hp i)) -
      finiteEntropy ((tupleLaw m p).map (tupleSum (fun k : Fin (n + 1) ↦ x k.val) m))
        (by simpa using (tupleLaw_support_finite m p hp).image (tupleSum (fun k : Fin (n + 1) ↦ x k.val) m)) ≤
      27 * m * ∑ i, (VarianceEnergy.energy ((p i).map (fun k ↦ x k.val)).toMeasure).toReal := by
  let P := tupleLaw m p
  let hP := tupleLaw_support_finite m p hp
  let s := tupleSum (fun k : Fin (n + 1) ↦ x k.val) m
  let d (ij : Fin m × Fin n) := orderedGapLength x n ij.2
  have hd (ij : Fin m × Fin n) : 0 < d ij := grid_gap_pos x hx ij.2
  have hsep : Set.InjOn (fun a ij ↦ tupleGridSide m n ij a) P.support :=
    (tupleGridSide_separates m n).injOn
  have hI := integral_revealedEntropyRate P hP s (tupleGridSide m n) d hd hsep
  have hF := integrableOn_revealedEntropyRate P hP s (tupleGridSide m n) d hd hsep
  have hG (i : Fin m) : IntegrableOn (cutDispersion (p i) (hp i) x) (Ioi 0) :=
    integrableOn_ordered_cutDispersion (p i) (hp i) x hx
  have hsum : IntegrableOn (fun t ↦ ∑ i, cutDispersion (p i) (hp i) x t) (Ioi 0) :=
    integrable_finsetSum _ (fun i _ ↦ hG i)
  have hbound := integral_mono_ae hF (hsum.const_mul (9 * m)) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact grid_revealedEntropyRate_le p hp x hx.monotone ht.le)
  rw [hI, integral_const_mul, integral_finsetSum _ (fun i _ ↦ hG i)] at hbound
  have henergy := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦
    integral_ordered_cutDispersion_le_three_energy (p i) (hp i) x hx)
  have hmul := mul_le_mul_of_nonneg_left henergy (by positivity : (0 : ℝ) ≤ 9 * m)
  have he := hbound.trans hmul
  change finiteEntropy (tupleLaw m p) (tupleLaw_support_finite m p hp) -
    finiteEntropy ((tupleLaw m p).map s) _ ≤ _ at he
  rw [finiteEntropy_tupleLaw m p hp] at he
  apply he.trans_eq
  rw [← Finset.mul_sum]
  ring

theorem ordered_entropy_loss_le_thirty {m n : ℕ}
    (p : Fin m → PMF (Fin (n + 1))) (hp : ∀ i, (p i).support.Finite) (x : ℕ → ℝ)
    (hx : StrictMono (fun k : Fin (n + 1) ↦ x k.val)) :
    (∑ i, finiteEntropy (p i) (hp i)) -
      finiteEntropy ((tupleLaw m p).map (tupleSum (fun k : Fin (n + 1) ↦ x k.val) m))
        (by simpa using (tupleLaw_support_finite m p hp).image (tupleSum (fun k : Fin (n + 1) ↦ x k.val) m)) ≤
      30 * m * ∑ i, (VarianceEnergy.energy ((p i).map (fun k ↦ x k.val)).toMeasure).toReal := by
  apply (ordered_entropy_loss_le_twenty_seven p hp x hx).trans
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num : (27 : ℝ) ≤ 30) (Nat.cast_nonneg m))
    (Finset.sum_nonneg (fun _ _ ↦ ENNReal.toReal_nonneg))

end ExactOverlaps.Entropy
