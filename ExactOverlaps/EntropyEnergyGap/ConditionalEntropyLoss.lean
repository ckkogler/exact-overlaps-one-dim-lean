module

public import ExactOverlaps.EntropyEnergyGap.ProductAverages
public import ExactOverlaps.EntropyEnergyGap.EntropyAverages
public import ExactOverlaps.Entropy.EntropyLoss

/-!
# Entropy loss after coordinatewise conditioning of independent copies

Theorem 1.3 applies to the genuine conditional product laws. Averaging
over the actual joint observation fibers recovers each marginal conditional
entropy and energy; the sum's conditional entropy is at most its entropy.
-/

@[expose] public section

open scoped BigOperators Classical
open ExactOverlaps.Entropy ExactOverlaps.FiniteProbability ExactOverlaps.VarianceEnergy

namespace ExactOverlaps.EntropyEnergyGap

noncomputable def tupleSumEntropy (m : ℕ) (q : PMF (FiniteTuple ℝ m))
    (hq : q.support.Finite) : ℝ :=
  finiteEntropy (q.map (tupleSum id m)) (by simpa using hq.image (tupleSum id m))

noncomputable def tupleMarginalEntropy (m : ℕ) (q : PMF (FiniteTuple ℝ m))
    (hq : q.support.Finite) : ℝ :=
  ∑ i, coordinateFunctional m i (fun p hp ↦ finiteEntropy p hp) q hq

noncomputable def tupleMarginalEnergy (m : ℕ) (q : PMF (FiniteTuple ℝ m))
    (hq : q.support.Finite) : ℝ :=
  ∑ i, coordinateFunctional m i (fun p _ ↦ (energy p.toMeasure).toReal) q hq

lemma tuple_entropy_loss_le (m : ℕ) (p : Fin m → PMF ℝ)
    (hp : ∀ i, (p i).support.Finite) :
    tupleMarginalEntropy m (tupleLaw m p) (tupleLaw_support_finite m p hp) ≤
      tupleSumEntropy m (tupleLaw m p) (tupleLaw_support_finite m p hp) +
        30 * m * tupleMarginalEnergy m (tupleLaw m p) (tupleLaw_support_finite m p hp) := by
  unfold tupleMarginalEntropy tupleMarginalEnergy tupleSumEntropy
  simp_rw [coordinateFunctional_tupleLaw m p hp]
  have h := entropy_loss_le_thirty m p hp
  linarith

lemma conditional_tuple_entropy_loss_le {β : Type*} (m : ℕ) (p : Fin m → PMF ℝ)
    (hp : ∀ i, (p i).support.Finite) (f : Fin m → ℝ → β)
    (b : ((tupleLaw m p).map (tupleMap m f)).support) :
    tupleMarginalEntropy m (conditionalPMF (tupleLaw m p) (tupleMap m f) b)
      (conditionalPMF_support_finite _ (tupleLaw_support_finite m p hp) _ b) ≤
    tupleSumEntropy m (conditionalPMF (tupleLaw m p) (tupleMap m f) b)
      (conditionalPMF_support_finite _ (tupleLaw_support_finite m p hp) _ b) +
    30 * m * tupleMarginalEnergy m (conditionalPMF (tupleLaw m p) (tupleMap m f) b)
      (conditionalPMF_support_finite _ (tupleLaw_support_finite m p hp) _ b) := by
  obtain ⟨a, ha, hab⟩ := (PMF.mem_support_map_iff (tupleMap m f) (tupleLaw m p) b.val).mp b.property
  let w : (tupleLaw m p).support := ⟨a, ha⟩
  let μ (i : Fin m) := conditionalAt (p i) (f i) (tupleSupportCoordinate m p w i)
  have hμ (i : Fin m) : (μ i).support.Finite := conditionalPMF_support_finite (p i) (hp i) _ _
  have hq : conditionalPMF (tupleLaw m p) (tupleMap m f) b = tupleLaw m μ := by
    apply Eq.trans _ (conditionalAt_tupleLaw m p f w)
    unfold conditionalAt
    apply congrArg (conditionalPMF (tupleLaw m p) (tupleMap m f))
    exact Subtype.ext hab.symm
  rw [finiteFunctional_congr (tupleMarginalEntropy m) hq _ (tupleLaw_support_finite m μ hμ),
    finiteFunctional_congr (tupleSumEntropy m) hq _ (tupleLaw_support_finite m μ hμ),
    finiteFunctional_congr (tupleMarginalEnergy m) hq _ (tupleLaw_support_finite m μ hμ)]
  exact tuple_entropy_loss_le m μ hμ

theorem sum_conditional_entropy_le {β : Type*} (m : ℕ) (p : Fin m → PMF ℝ)
    (hp : ∀ i, (p i).support.Finite) (f : Fin m → ℝ → β) :
    (∑ i, conditionalEntropy (p i) (hp i) (f i)) ≤
      tupleSumEntropy m (tupleLaw m p) (tupleLaw_support_finite m p hp) +
        30 * m * ∑ i, meanFiberFunctional (p i) (hp i) (f i)
          (fun q _ ↦ (energy q.toMeasure).toReal) := by
  have h := meanFiberFunctional_mono (tupleLaw m p) (tupleLaw_support_finite m p hp)
    (tupleMap m f) (tupleMarginalEntropy m)
    (fun q hq ↦ tupleSumEntropy m q hq + 30 * m * tupleMarginalEnergy m q hq)
    (conditional_tuple_entropy_loss_le m p hp f)
  rw [meanFiberFunctional_add, meanFiberFunctional_const_mul] at h
  unfold tupleMarginalEntropy tupleMarginalEnergy at h
  rw [mean_product_coordinate_sum m p hp f, mean_product_coordinate_sum m p hp f] at h
  simp_rw [mean_entropy_eq_conditional] at h
  have hs := mean_map_entropy_le (tupleLaw m p) (tupleLaw_support_finite m p hp)
    (tupleMap m f) (tupleSum id m)
  exact h.trans (add_le_add hs le_rfl)

theorem iid_conditional_entropy_le {β : Type*} (m : ℕ) (p : PMF ℝ)
    (hp : p.support.Finite) (f : ℝ → β) :
    m * conditionalEntropy p hp f ≤
      tupleSumEntropy m (iidTupleLaw p m) (iidTupleLaw_support_finite p hp m) +
        30 * m ^ 2 * meanFiberFunctional p hp f (fun q _ ↦ (energy q.toMeasure).toReal) := by
  have h := sum_conditional_entropy_le m (fun _ ↦ p) (fun _ ↦ hp) (fun _ ↦ f)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  apply h.trans_eq
  congr 1
  ring

end ExactOverlaps.EntropyEnergyGap
