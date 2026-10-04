module

public import ExactOverlaps.Entropy.DiscreteMeasureConvolution
public import ExactOverlaps.Probability.IndependentExpectations

/-!
# Finite PMF products represent product measures

Restricting to the actual finite supports removes the countability
restriction on the ambient measurable spaces. Mapping the support laws
back gives the exact product measure and real convolution identities.
-/

@[expose] public section

open MeasureTheory
open scoped Classical
open ExactOverlaps.FiniteProbability

namespace ExactOverlaps.Entropy

lemma independentPair_toMeasure_of_finite {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (p : PMF α) (q : PMF β) (hp : p.support.Finite) (hq : q.support.Finite) :
    (independentPair p q).toMeasure = p.toMeasure.prod q.toMeasure := by
  let : Fintype p.support := hp.fintype
  let : Fintype q.support := hq.fintype
  have he : (independentPair (supportLaw p) (supportLaw q)).map
      (Prod.map Subtype.val Subtype.val) = independentPair p q := by
    exact (independentPair_map_pair (supportLaw p) (supportLaw q) Subtype.val Subtype.val).trans
      (by rw [supportLaw_map_val, supportLaw_map_val])
  rw [← he, ← PMF.toMeasure_map _ _ (measurable_subtype_coe.prodMap measurable_subtype_coe),
    independentPair_toMeasure, ← Measure.map_prod_map _ _ measurable_subtype_coe measurable_subtype_coe,
    PMF.toMeasure_map _ _ measurable_subtype_coe, PMF.toMeasure_map _ _ measurable_subtype_coe,
    supportLaw_map_val, supportLaw_map_val]

theorem finite_discreteConvolution_toMeasure (p q : PMF ℝ)
    (hp : p.support.Finite) (hq : q.support.Finite) :
    (discreteConvolution p q).toMeasure = p.toMeasure ∗ q.toMeasure := by
  rw [discreteConvolution, ← PMF.toMeasure_map _ _ measurable_add,
    independentPair_toMeasure_of_finite p q hp hq]
  rfl

end ExactOverlaps.Entropy
