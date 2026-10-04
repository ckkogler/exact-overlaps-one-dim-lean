/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.GaussianEntropyGrowth.GaussianAverage

/-!
# Gaussian entropy between fixed physical scales

The entropy difference between meshes one and C approaches log C as the
Gaussian standard deviation increases. The estimate holds for every
positive real C, so in particular it covers every integer scale ratio.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace ExactOverlaps.GaussianEntropyGrowth

open GaussianApproximation GaussianScaleEntropy

lemma entropyBetween_gaussian_error {σ C : ℝ} (hσ : 0 < σ) (hC : 0 < C) :
    |entropyBetween (centeredGaussian (NNReal.mk (σ ^ 2) (sq_nonneg σ))) 1 C -
      Real.log C| ≤ ((1 + C) * σ * gaussianFirstMoment + 1 + C ^ 2) / σ ^ 2 := by
  let G := centeredGaussian (NNReal.mk (σ ^ 2) (sq_nonneg σ))
  let h := gaussianDifferentialEntropy (NNReal.mk (σ ^ 2) (sq_nonneg σ))
  have h1 := entropy_gaussian_error_sigma hσ (show (0 : ℝ) < 1 by norm_num)
  have h2 := entropy_gaussian_error_sigma hσ hC
  have he : entropyBetween G 1 C - Real.log C =
      (entropy G 1 - h) - (entropy G C - (h - Real.log C)) := by
    unfold entropyBetween
    ring
  change |entropyBetween G 1 C - Real.log C| ≤ _
  rw [he]
  calc
    _ ≤ |entropy G 1 - h| + |entropy G C - (h - Real.log C)| := abs_sub _ _
    _ ≤ (σ * gaussianFirstMoment + 1) / σ ^ 2 +
        (σ * gaussianFirstMoment + C) * C / σ ^ 2 :=
      add_le_add (by simpa only [Real.log_one, sub_zero, mul_one] using h1) h2
    _ = _ := by ring

lemma gaussian_large_variance (C : ℝ) (hC : 0 < C) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : ℝ, 0 < S ∧ ∀ σ : ℝ, S ≤ σ →
      Real.log C - ε <
        entropyBetween (centeredGaussian (NNReal.mk (σ ^ 2) (sq_nonneg σ))) 1 C := by
  let D := (1 + C) * gaussianFirstMoment + 1 + C ^ 2
  refine ⟨max 1 (2 * D / ε), lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro σ hS
  have hσ1 : 1 ≤ σ := (le_max_left _ _).trans hS
  have hσ : 0 < σ := lt_of_lt_of_le (by norm_num) hσ1
  have hb : 1 + C ^ 2 ≤ (1 + C ^ 2) * σ :=
    le_mul_of_one_le_right (by positivity) hσ1
  have hrate : ((1 + C) * σ * gaussianFirstMoment + 1 + C ^ 2) / σ ^ 2 ≤ D / σ := by
    calc
      _ ≤ (D * σ) / σ ^ 2 := div_le_div_of_nonneg_right (by dsimp [D]; nlinarith) (sq_nonneg σ)
      _ = D / σ := by field_simp
  have hsize : 2 * D / ε ≤ σ := (le_max_right _ _).trans hS
  have heps : D / σ ≤ ε / 2 := by
    apply (div_le_iff₀ hσ).mpr
    have := (div_le_iff₀ hε).mp hsize
    nlinarith
  have herror := (entropyBetween_gaussian_error hσ hC).trans (hrate.trans heps)
  have := (abs_le.mp herror).1
  linarith

end ExactOverlaps.GaussianEntropyGrowth
