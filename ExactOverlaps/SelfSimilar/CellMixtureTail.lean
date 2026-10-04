module

public import ExactOverlaps.SelfSimilar.CellMixtureEntropy

/-!
A mixture of whole-cell laws with high entropy has few low-entropy cells.
The exceptional probability is controlled by the total discarded branch
weight. This avoids replacing conditional laws by an assumed approximation.
-/

@[expose] public section

open scoped Classical ENNReal BigOperators

namespace ExactOverlaps.Entropy

theorem finite_sum_pmf_toReal_le_one {α : Type*} (p : PMF α) (s : Finset α) :
    (∑ a ∈ s, (p a).toReal) ≤ 1 := by
  rw [← ENNReal.toReal_sum (fun a _ ↦ p.apply_ne_top a)]
  apply ENNReal.toReal_le_of_le_ofReal zero_le_one
  simpa only [ENNReal.ofReal_one, p.tsum_coe] using ENNReal.sum_le_tsum (f := p) s

noncomputable def finiteConditionalBelowMass {α β : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (A : ℝ) : ℝ :=
  letI : Fintype (p.map f).support := (show (p.map f).support.Finite from by
    simpa using hp.image f).fintype
  ∑ b : (p.map f).support,
    if finiteEntropy (conditionalPMF p f b) (conditionalPMF_support_finite p hp f b) ≤ A
      then ((p.map f) b).toReal else 0

theorem finite_mixture_below_mass_le {ι α β : Type*} [Fintype ι]
    (p : PMF ι) (q : ι → PMF α) (hq : ∀ i, (q i).support.Finite)
    (f : α → β) (G : Finset ι) {A γ : ℝ} (hA : 0 ≤ A)
    (hgood : ∀ i ∈ G, (∃ c : β, ∀ a ∈ (q i).support, f a = c) ∧
      A ≤ finiteEntropy (q i) (hq i)) :
    γ * finiteConditionalBelowMass (p.bind q) (bind_support_finite p q hq) f (A - γ) ≤
      A * (∑ i, if i ∈ G then 0 else (p i).toReal) := by
  let r := p.bind q
  let hr : r.support.Finite := bind_support_finite p q hq
  let hf : (r.map f).support.Finite := by simpa using hr.image f
  let : Fintype (r.map f).support := hf.fintype
  let B (b : (r.map f).support) : ℝ :=
    ∑ i, if i ∈ G then 0 else (p i).toReal * ((q i).map f b).toReal
  have hB (b : (r.map f).support) : 0 ≤ B b := by
    apply Finset.sum_nonneg
    intro i _
    split_ifs <;> positivity
  have hsum (b : β) : (∑ i, (p i).toReal * ((q i).map f b).toReal) =
      ((r.map f) b).toReal := by
    dsimp [r]
    rw [PMF.map_bind, bind_toReal]
  have hcell (b : (r.map f).support) :
      A * ((r.map f) b).toReal ≤ ((r.map f) b).toReal *
        finiteEntropy (conditionalPMF r f b) (conditionalPMF_support_finite r hr f b) + A * B b := by
    have hpoint (i : ι) : A * ((p i).toReal * ((q i).map f b).toReal) ≤
        (p i).toReal * ((q i).map f b).toReal *
          finiteEntropy (conditionalOrSelf (q i) f b)
            (conditionalOrSelf_support_finite (q i) (hq i) f b) +
          A * (if i ∈ G then 0 else (p i).toReal * ((q i).map f b).toReal) := by
      have hw : 0 ≤ (p i).toReal * ((q i).map f b).toReal := by positivity
      by_cases hi : i ∈ G
      · obtain ⟨⟨c, hc⟩, hent⟩ := hgood i hi
        simp only [hi, ite_true, mul_zero, add_zero,
          conditionalOrSelf_eq_of_constant (q i) f hc b]
        have ht := mul_le_mul_of_nonneg_left hent hw
        nlinarith
      · simp only [hi, ite_false]
        have hh := mul_nonneg hw (finiteEntropy_nonneg
          (conditionalOrSelf (q i) f b) (conditionalOrSelf_support_finite (q i) (hq i) f b))
        linarith
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hpoint i)
    simp only [← Finset.mul_sum, Finset.sum_add_distrib, hsum] at hs
    have hc := cell_mixture_entropy_concavity p q hq f b
    dsimp [B]
    linarith
  have hpoint (b : (r.map f).support) :
      γ * (if finiteEntropy (conditionalPMF r f b)
        (conditionalPMF_support_finite r hr f b) ≤ A - γ then ((r.map f) b).toReal else 0) ≤ A * B b := by
    split_ifs with hb
    · have hmul := mul_le_mul_of_nonneg_left hb
        (show 0 ≤ ((r.map f) b).toReal from ENNReal.toReal_nonneg)
      have hc := hcell b
      nlinarith
    · simpa only [mul_zero] using mul_nonneg hA (hB b)
  have htotal : (∑ b : (r.map f).support, B b) ≤ ∑ i, if i ∈ G then 0 else (p i).toReal := by
    have hmass (i : ι) : (∑ b : (r.map f).support, ((q i).map f b).toReal) ≤ 1 := by
      rw [← Finset.sum_subtype hf.toFinset
        (by simp : ∀ b, b ∈ hf.toFinset ↔ b ∈ (r.map f).support)
        (fun b : β ↦ ((q i).map f b).toReal)]
      exact finite_sum_pmf_toReal_le_one ((q i).map f) hf.toFinset
    calc
      _ = ∑ i, if i ∈ G then 0 else (p i).toReal *
          (∑ b : (r.map f).support, ((q i).map f b).toReal) := by
        dsimp [B]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        split_ifs with hi
        · simp only [Finset.sum_const_zero]
        · simp only [Finset.mul_sum]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs with hi
        · rfl
        · simpa only [mul_one] using mul_le_mul_of_nonneg_left (hmass i) ENNReal.toReal_nonneg
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun b _ ↦ hpoint b)
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hs
  exact hs.trans (mul_le_mul_of_nonneg_left htotal hA)

end ExactOverlaps.Entropy
