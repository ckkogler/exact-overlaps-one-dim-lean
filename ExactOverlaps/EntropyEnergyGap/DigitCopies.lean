module

public import ExactOverlaps.DigitSums.ArrayLaw
public import ExactOverlaps.Entropy.FiniteProductSumMap
public import ExactOverlaps.Probability.FiniteProductDispersion
public import ExactOverlaps.Probability.FiberAverages

/-!
# Exact digit-array realization of independent copies

An arbitrary finite law on a digit vector is copied independently. Mapping
the actual tuple of vectors to its rectangular array identifies the sum
law with the array sum counted in `DigitSums.ArrayLaw`.
-/

@[expose] public section

open scoped BigOperators Classical
open ExactOverlaps.Entropy ExactOverlaps.FiniteProbability ExactOverlaps.DigitSums

namespace ExactOverlaps.EntropyEnergyGap

def digitValueSum {α ι : Type*} [Fintype ι] (v : ι → α → ℝ) (a : ι → ℝ)
    (z : ι → α) : ℝ := ∑ j, a j * v j (z j)

lemma copied_digit_sum_law {α ι : Type*} [Fintype ι]
    (v : ι → α → ℝ) (a : ι → ℝ) (ν : PMF (ι → α)) (m : ℕ) :
    (iidTupleLaw (ν.map (digitValueSum v a)) m).map (tupleSum id m) =
      ((iidTupleLaw ν m).map (fun w i ↦ tupleCoordinate m w i)).map (arraySum v a m) := by
  unfold iidTupleLaw
  rw [tupleLaw_sum_map m (fun _ ↦ ν) (digitValueSum v a) id, PMF.map_comp]
  congr 1
  funext w
  rw [ExactOverlaps.FiniteLaw.tupleSum_eq_sum_coordinates]
  rfl

theorem copied_digit_sum_entropy_le {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι]
    (v : ι → α → ℝ) (a : ι → ℝ) (a₀ : α) (ν : PMF (ι → α)) (m : ℕ)
    (hp : (ν.map (digitValueSum v a)).support.Finite) :
    finiteEntropy ((iidTupleLaw (ν.map (digitValueSum v a)) m).map (tupleSum id m))
      (by simpa using (iidTupleLaw_support_finite _ hp m).image (tupleSum id m)) ≤
      (Fintype.card ι : ℝ) * (Fintype.card α - 1 : ℕ) * Real.log (m + 1 : ℝ) := by
  have he := finiteFunctional_congr (fun q hq ↦ finiteEntropy q hq)
    (copied_digit_sum_law v a ν m)
    (by simpa using (iidTupleLaw_support_finite _ hp m).image (tupleSum id m))
    (arraySumLaw_support_finite v a m ((iidTupleLaw ν m).map (fun w i ↦ tupleCoordinate m w i)))
  rw [he]
  exact arraySumLaw_entropy_le v a a₀ m ((iidTupleLaw ν m).map (fun w i ↦ tupleCoordinate m w i))

end ExactOverlaps.EntropyEnergyGap
