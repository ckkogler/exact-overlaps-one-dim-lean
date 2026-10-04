/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.Entropy.GaussianCentralMass
public import ExactOverlaps.Entropy.AtomicVariance

/-!
# Uniform local entropy for a family of Gaussian laws

For variance in a fixed positive interval, a common sufficiently fine dyadic
level gives nearly uniform components on a finite set of central labels of
large probability. The level is independent of the Gaussian mean.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace ExactOverlaps.Entropy

theorem gaussian_local_uniformity {σ V δ : ℝ} (hσ : 0 < σ) (_hV : 0 < V)
    (hδ : 0 < δ) {m : ℕ} (hm : 0 < m) :
    ∃ R > 0, ∃ p : ℕ, ∀ i : ℕ, p ≤ i → ∀ (b : ℝ) (v : ℝ≥0),
      σ ≤ (v : ℝ) → (v : ℝ) ≤ V →
      (1 - δ < ∑ k ∈ Finset.Icc (dyadicQuantize i (b - R)) (dyadicQuantize i (b + R)),
        ((dyadicLaw (gaussianProbability b v) i) k).toReal) ∧
      (∀ k : (dyadicLaw (gaussianProbability b v) i).support,
        k.val ∈ Icc (dyadicQuantize i (b - R)) (dyadicQuantize i (b + R)) →
        1 - δ < normalizedDyadicEntropy (rescaledComponent (gaussianProbability b v) i k)
          (rescaledComponent_hasBoundedSupport (gaussianProbability b v) i k) m) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (V / δ))
  let R : ℝ := N
  have hR1 : 1 < R := (le_max_left _ _).trans_lt hN
  have hR : 0 < R := lt_trans zero_lt_one hR1
  have htail : V / R ^ 2 < δ := by
    have hVR : V / δ < R := (le_max_right _ _).trans_lt hN
    have hVmul := (div_lt_iff₀ hδ).1 hVR
    apply (div_lt_iff₀ (sq_pos_of_pos hR)).2
    nlinarith [mul_pos hδ (sub_pos.mpr hR1)]
  have hd : 0 < (m : ℝ) * Real.log 2 :=
    mul_pos (Nat.cast_pos.mpr hm) (Real.log_pos (by norm_num))
  let η : ℝ := δ * σ * ((m : ℝ) * Real.log 2) / (2 * (R + 1))
  have hη : 0 < η := by dsimp only [η]; positivity
  obtain ⟨p, _hp, hpη⟩ := exists_positive_dyadic_depth hη
  refine ⟨R, hR, p, ?_⟩
  intro i hpi b v hvσ hvV
  have hmass := gaussian_central_labels_mass_ge b v i hR
  have ht := div_le_div_of_nonneg_right hvV (sq_nonneg R)
  have hi : (2 : ℝ) ^ (-(i : ℤ)) < η := by
    apply lt_of_le_of_lt _ hpη
    exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  have he : (2 * (R + 1) * (2 : ℝ) ^ (-(i : ℤ)) / σ) /
      ((m : ℝ) * Real.log 2) < δ := by
    apply (div_lt_iff₀ hd).2
    apply (div_lt_iff₀ hσ).2
    have hi' := (lt_div_iff₀ (show 0 < 2 * (R + 1) by positivity)).1 hi
    nlinarith
  refine ⟨by linarith, ?_⟩
  intro k hk
  have hb := gaussian_central_component_entropy_ge b v hσ hvσ i k hm hk
  linarith

end ExactOverlaps.Entropy
