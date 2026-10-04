module

public import ExactOverlaps.SelfSimilar.CellMixtureTail
public import ExactOverlaps.SelfSimilar.UniformEntropyCriterion
public import ExactOverlaps.Entropy.DyadicMixture
public import ExactOverlaps.SelfSimilar.SimilarityLaws

/-! The finite whole-cell mixture estimate expressed for genuine dyadic components. -/

@[expose] public section

open MeasureTheory Set
open scoped Classical ENNReal BigOperators

namespace ExactOverlaps.Entropy

theorem componentEntropyBelowMass_eq_finite (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) {m : ℕ} (hm : 0 < m) (d δ : ℝ) :
    componentEntropyBelowMass μ hμ i m d δ =
      finiteConditionalBelowMass (dyadicLaw μ (i + m)) (dyadicLaw_support_finite μ hμ (i + m))
        (fun j : ℤ ↦ j / (2 ^ m : ℕ)) ((d - δ) * ((m : ℝ) * Real.log 2)) := by
  let : Fintype (dyadicLaw μ i).support := (dyadicLaw_support_finite μ hμ i).fintype
  let : Fintype ((dyadicLaw μ (i + m)).map (fun j : ℤ ↦ j / (2 ^ m : ℕ))).support :=
    (show ((dyadicLaw μ (i + m)).map (fun j : ℤ ↦ j / (2 ^ m : ℕ))).support.Finite
      from by simpa using ((dyadicLaw_support_finite μ hμ (i + m)).image
        (fun j : ℤ ↦ j / (2 ^ m : ℕ)))).fintype
  let e : (dyadicLaw μ i).support ≃
      ((dyadicLaw μ (i + m)).map (fun j : ℤ ↦ j / (2 ^ m : ℕ))).support :=
    { toFun := fun k ↦ ⟨k, by simpa only [dyadicLaw_map_div] using k.property⟩
      invFun := fun k ↦ ⟨k, by simpa only [dyadicLaw_map_div] using k.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  unfold componentEntropyBelowMass finiteConditionalBelowMass
  apply Fintype.sum_equiv e
  intro k
  have hden : 0 < (m : ℝ) * Real.log 2 :=
    mul_pos (Nat.cast_pos.mpr hm) (Real.log_pos (by norm_num))
  have he : (e k : ℤ) = k := rfl
  have hent : finiteEntropy
      (conditionalPMF (dyadicLaw μ (i + m)) (fun j : ℤ ↦ j / (2 ^ m : ℕ)) (e k))
      (conditionalPMF_support_finite _ (dyadicLaw_support_finite μ hμ (i + m)) _ (e k)) =
      dyadicEntropy (rescaledComponent μ i k) (rescaledComponent_hasBoundedSupport μ i k) m := by
    rw [dyadicEntropy_rescaledComponent]
    simp only [dyadicEntropy, dyadicLaw_rawComponent]
    rfl
  simp only [hent, he, dyadicLaw_map_div, normalizedDyadicEntropy, div_le_iff₀ hden]

theorem dyadic_fine_support_coarse_constant (μ : ProbabilityMeasure ℝ) (i : ℤ)
    (m : ℕ) {k : ℤ} (hk : ∀ᵐ x ∂(μ : Measure ℝ), dyadicQuantize i x = k) :
    ∀ j ∈ (dyadicLaw μ (i + m)).support, j / (2 ^ m : ℕ) = k := by
  intro j hj
  by_contra hne
  apply hj
  rw [dyadicLaw_apply]
  apply measure_mono_null (t := {x | dyadicQuantize i x ≠ k})
  · intro x hx hxe
    apply hne
    change dyadicQuantize (i + m) x = j at hx
    rw [← hx, ← dyadicQuantize_add_nat]
    exact hxe
  · exact ae_iff.mp hk

theorem dyadic_mixture_below_mass_le {ι : Type*} [Fintype ι]
    (p : PMF ι) (ν : ι → ProbabilityMeasure ℝ) (hν : ∀ j, HasBoundedSupport (ν j))
    (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ)
    (hmix : (μ : Measure ℝ) = ∑ j, p j • (ν j : Measure ℝ))
    (i : ℤ) {m : ℕ} (hm : 0 < m) (G : Finset ι) {d δ : ℝ}
    (hA : 0 ≤ d - δ / 2)
    (hgood : ∀ j ∈ G, (∃ k : ℤ, ∀ᵐ x ∂(ν j : Measure ℝ), dyadicQuantize i x = k) ∧
      (d - δ / 2) * ((m : ℝ) * Real.log 2) ≤ dyadicEntropy (ν j) (hν j) (i + m)) :
    (δ / 2) * componentEntropyBelowMass μ hμ i m d δ ≤
      (d - δ / 2) * (∑ j, if j ∈ G then 0 else (p j).toReal) := by
  let D : ℝ := (m : ℝ) * Real.log 2
  have hD : 0 < D := mul_pos (Nat.cast_pos.mpr hm) (Real.log_pos (by norm_num))
  let q : ι → PMF ℤ := fun j ↦ dyadicLaw (ν j) (i + m)
  let hq : ∀ j, (q j).support.Finite := fun j ↦ dyadicLaw_support_finite (ν j) (hν j) (i + m)
  have hfg : ∀ j ∈ G, (∃ c : ℤ, ∀ a ∈ (q j).support, a / (2 ^ m : ℕ) = c) ∧
      (d - δ / 2) * D ≤ finiteEntropy (q j) (hq j) := by
    intro j hj
    obtain ⟨⟨k, hk⟩, hent⟩ := hgood j hj
    exact ⟨⟨k, dyadic_fine_support_coarse_constant (ν j) i m hk⟩, hent⟩
  have h := finite_mixture_below_mass_le p q hq (fun j : ℤ ↦ j / (2 ^ m : ℕ)) G
    (γ := (δ / 2) * D) (mul_nonneg hA hD.le) hfg
  have hbind : p.bind q = dyadicLaw μ (i + m) :=
    (dyadicLaw_eq_bind_of_measure_eq p ν μ hmix (i + m)).symm
  have he : (d - δ / 2) * D - δ / 2 * D = (d - δ) * D := by ring
  simp only [hbind, he] at h
  rw [← componentEntropyBelowMass_eq_finite μ hμ i hm d δ] at h
  nlinarith

end ExactOverlaps.Entropy
