module

public import ExactOverlaps.VarianceEnergy.FiniteSupport
public import ExactOverlaps.VarianceEnergy.Tail

/-!
# Finite energy of finite laws

Small-scale vanishing and the integrable large-scale bound prove finiteness
before any conversion of variance energy to a real number.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace ExactOverlaps.VarianceEnergy

lemma energy_eq_energyBelow_add_energyAbove (μ : Measure ℝ) {R : ℝ} (hR : 0 < R) :
    energy μ = energyBelow μ R + energyAbove μ R := by
  unfold energy energyBelow energyAbove
  rw [← Ioo_union_Ici_eq_Ioi hR,
    lintegral_union measurableSet_Ici (Set.disjoint_left.mpr (fun _ hx hy ↦
      (not_lt_of_ge hy) hx.2)), ← restrict_Ioi_eq_restrict_Ici]

lemma energy_le_energyBelow_add_tail (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {b D R : ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ Icc b (b + D)) (hR : 0 < R) :
    energy μ ≤ energyBelow μ R + ENNReal.ofReal (D ^ 2 / (2 * R ^ 2)) := by
  rw [energy_eq_energyBelow_add_energyAbove μ hR]
  exact add_le_add le_rfl (energyAbove_support_le μ hμ hR)

lemma energyBelow_eq_zero_of_vanishing (μ : Measure ℝ) {δ : ℝ}
    (hδ : ∀ r ≤ δ, normalizedLocalVariance μ r = 0) : energyBelow μ δ = 0 := by
  apply setLIntegral_eq_zero measurableSet_Ioo
  intro r hr
  simp [hδ r hr.2.le]

lemma energy_ne_top_of_finite_support (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (s : Finset ℝ) (hμ : ∀ᵐ x ∂μ, x ∈ s) : energy μ ≠ ∞ := by
  obtain ⟨δ, hδ, hvanish⟩ := exists_pos_vanishing_scale μ s hμ
  obtain ⟨b, D, hsupp⟩ := exists_support_interval μ s hμ
  rw [energy_eq_energyBelow_add_energyAbove μ hδ,
    energyBelow_eq_zero_of_vanishing μ hvanish, zero_add]
  exact energyAbove_ne_top μ hsupp hδ

lemma energyBelow_ne_top_of_finite_support (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (s : Finset ℝ) (hμ : ∀ᵐ x ∂μ, x ∈ s) (R : ℝ) : energyBelow μ R ≠ ∞ :=
  ne_of_lt ((energyBelow_le_energy μ R).trans_lt
    (lt_top_iff_ne_top.mpr (energy_ne_top_of_finite_support μ s hμ)))

/-- The real-valued tail estimate, after finiteness of the finite law is established. -/
lemma energy_toReal_sub_energyBelow_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (s : Finset ℝ) (hs : ∀ᵐ x ∂μ, x ∈ s) {b D R : ℝ}
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc b (b + D)) (hR : 0 < R) :
    (energy μ).toReal - (energyBelow μ R).toReal ≤ D ^ 2 / (2 * R ^ 2) := by
  have heq := congrArg ENNReal.toReal (energy_eq_energyBelow_add_energyAbove μ hR)
  rw [ENNReal.toReal_add (energyBelow_ne_top_of_finite_support μ s hs R)
    (energyAbove_ne_top μ hμ hR)] at heq
  have hbound := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (energyAbove_support_le μ hμ hR)
  rw [ENNReal.toReal_ofReal (by positivity)] at hbound
  linarith

end ExactOverlaps.VarianceEnergy
