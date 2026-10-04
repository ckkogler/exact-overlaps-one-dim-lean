/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.WImprovement.FiniteLawProfiles
public import ExactOverlaps.WImprovement.GridSampling
public import Mathlib.Data.Finset.Sort

/-!
# Separated physical scales carrying finite-law variance

A positive lower bound on the actual averaged truncated variance energy
produces a nonempty increasing finite list of physical scales below the
cutoff. Their separation and sampled variance sum retain the exact grid
period and averaging constant.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ExactOverlaps.WImprovement

open VarianceEnergy

lemma exists_separated_variance_scales {ι : Type*} [Fintype ι]
    (q : PMF ι) (p : ι → PMF ℝ) (hp : ∀ i, (p i).support.Finite)
    {R d η : ℝ} (hR : 0 < R) (hd : 0 < d) (hη : 0 ≤ η)
    (henergy : d * η < ∑ i, (q i).toReal * (energyBelow (p i).toMeasure R).toReal) :
    ∃ m : ℕ, 0 < m ∧ ∃ s : Fin m → ℝ, StrictMono s ∧
      (∀ i, 0 < s i ∧ s i < R) ∧
      (∀ i j, i < j → Real.exp d * s i ≤ s j) ∧
      η < ∑ i, meanVarianceProfile q p (s i) := by
  classical
  obtain ⟨δ, hδ, hz⟩ := exists_meanLogVarianceProfile_cutoff q p hp
  have hi := integrable_meanLogVarianceProfile q p hp R
  have ha : d * η < ∫ u, meanLogVarianceProfile q p R u := by
    rwa [integral_meanLogVarianceProfile q p hp]
  obtain ⟨u, hu, t, ht, hpoints, hsum⟩ := exists_compact_grid_sample hi
    (meanLogVarianceProfile_nonneg q p R) (Real.log δ) (Real.log R)
    (hz R hR) hd hη ha
  let e : Fin t.card ↪o ℕ := t.orderEmbOfFin rfl
  let g : ℕ → ℝ := fun j ↦ Real.exp (Real.log δ + u + (j : ℝ) * d)
  have heg (i : Fin t.card) : e i ∈ t := t.orderEmbOfFin_mem rfl i
  have hgR (j : ℕ) (hj : j ∈ t) : g j < R := by
    exact (Real.exp_lt_exp.mpr (hpoints j hj).2).trans_eq (Real.exp_log hR)
  refine ⟨t.card, Finset.card_pos.mpr ht, fun i ↦ g (e i),
    (exp_grid_strictMono (Real.log δ) u hd).comp e.strictMono, ?_, ?_, ?_⟩
  · intro i
    exact ⟨Real.exp_pos _, hgR _ (heg i)⟩
  · intro i j hij
    exact exp_grid_separation (Real.log δ) u hd.le (e.strictMono hij)
  · have hterm (j : ℕ) (hj : j ∈ t) :
        meanLogVarianceProfile q p R (Real.log δ + u + (j : ℝ) * d) =
          meanVarianceProfile q p (g j) := by
      rw [meanLogVarianceProfile_eq, ite_eq_left (hgR j hj)]
    have hs : (∑ j ∈ t, meanLogVarianceProfile q p R
        (Real.log δ + u + (j : ℝ) * d)) = ∑ j ∈ t, meanVarianceProfile q p (g j) :=
      Finset.sum_congr rfl hterm
    rw [hs] at hsum
    have he : (∑ i : Fin t.card, meanVarianceProfile q p (g (e i))) =
        ∑ j ∈ t, meanVarianceProfile q p (g j) := by
      calc
        _ = ∑ j ∈ Finset.univ.image e, meanVarianceProfile q p (g j) :=
          (Finset.sum_image (fun i _ j _ hij ↦ e.injective hij)).symm
        _ = _ := by rw [t.image_orderEmbOfFin_univ rfl]
    rwa [he]

end ExactOverlaps.WImprovement
