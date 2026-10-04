module

public import ExactOverlaps.Entropy.OrderedEntropyLoss
public import ExactOverlaps.Entropy.FiniteProductSumMap
public import ExactOverlaps.Probability.CommonOrderedPresentation

/-!
# Entropy loss under addition of independent finite real laws

This is the finite-law form of Theorem 1.3. The sum law is the push-forward
of the actual independent product PMF. A common increasing support grid
preserves the laws, entropies, sum law and variance energies exactly.
-/

@[expose] public section

open scoped BigOperators Classical
open ExactOverlaps.Poisson ExactOverlaps.FiniteProbability

namespace ExactOverlaps.Entropy

theorem entropy_loss_le_thirty (m : ℕ) (p : Fin m → PMF ℝ)
    (hp : ∀ i, (p i).support.Finite) :
    (∑ i, finiteEntropy (p i) (hp i)) -
      finiteEntropy ((tupleLaw m p).map (tupleSum id m))
        (by simpa using (tupleLaw_support_finite m p hp).image (tupleSum id m)) ≤
      30 * m * ∑ i, (VarianceEnergy.energy (p i).toMeasure).toReal := by
  let O := commonOrderedPresentation p hp
  let q := O.law
  have hq (i : Fin m) : (q i).support.Finite := Set.toFinite _
  let f : Fin (O.size + 1) → ℝ := fun k ↦ O.coordinate k.val
  have hmap : (fun i ↦ (q i).map f) = p := funext O.map_eq
  have hent (i : Fin m) : finiteEntropy (q i) (hq i) = finiteEntropy (p i) (hp i) := by
    have h := finiteEntropy_map_of_injective (q i) (hq i) O.strictlyOrdered.injective
    have hm : (q i).map f = p i := O.map_eq i
    exact h.symm.trans (finiteFunctional_congr (fun r hr ↦ finiteEntropy r hr) hm _ _)
  have hsum := tupleLaw_sum_map m q f id
  rw [hmap] at hsum
  have hsEntropy :
      finiteEntropy ((tupleLaw m q).map (tupleSum f m))
        (by simpa using (tupleLaw_support_finite m q hq).image (tupleSum f m)) =
      finiteEntropy ((tupleLaw m p).map (tupleSum id m))
        (by simpa using (tupleLaw_support_finite m p hp).image (tupleSum id m)) :=
    finiteFunctional_congr (fun r hr ↦ finiteEntropy r hr) hsum.symm _ _
  have h := ordered_entropy_loss_le_thirty q hq O.coordinate O.strictlyOrdered
  change (∑ i, finiteEntropy (q i) (hq i)) -
    finiteEntropy ((tupleLaw m q).map (tupleSum f m)) _ ≤ _ at h
  rw [hsEntropy] at h
  have hm (i : Fin m) : (q i).map (fun k ↦ O.coordinate k.val) = p i := O.map_eq i
  simpa only [hent, hm] using h

end ExactOverlaps.Entropy
