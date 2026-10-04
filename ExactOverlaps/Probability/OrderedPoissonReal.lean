module

public import ExactOverlaps.Probability.FinitePoissonReal
public import ExactOverlaps.Probability.GridGeometry

/-!
# Ordinary dispersion integrals on a prescribed finite grid

The ordered Poisson energy bound implies genuine real integrability on
any prescribed increasing finite grid, allowing unused grid atoms.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ExactOverlaps.Poisson

lemma ordered_cutDispersion_ae_nonneg {n : ℕ} (p : PMF (Fin (n + 1)))
    (hp : p.support.Finite) (x : ℕ → ℝ)
    (hx : Monotone (fun k : Fin (n + 1) ↦ x k.val)) :
    ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), 0 ≤ cutDispersion p hp x t := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact cutDispersion_nonneg p hp x (grid_monotoneOn x hx) ht.le

lemma ordered_lintegral_cutDispersion_ne_top {n : ℕ} (p : PMF (Fin (n + 1)))
    (hp : p.support.Finite) (x : ℕ → ℝ)
    (hx : StrictMono (fun k : Fin (n + 1) ↦ x k.val)) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (cutDispersion p hp x t)) ≠ ∞ := by
  let q : PMF ℝ := p.map (fun k : Fin (n + 1) ↦ x k.val)
  have hq : q.support.Finite := by simpa [q] using hp.image (fun k : Fin (n + 1) ↦ x k.val)
  have hne := finiteLaw_energy_ne_top q hq
  have hb := lintegral_cutDispersion_le_three_energy p hp x hx
  exact ne_of_lt (hb.trans_lt (lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top (by norm_num) hne)))

theorem integrableOn_ordered_cutDispersion {n : ℕ} (p : PMF (Fin (n + 1)))
    (hp : p.support.Finite) (x : ℕ → ℝ)
    (hx : StrictMono (fun k : Fin (n + 1) ↦ x k.val)) :
    IntegrableOn (cutDispersion p hp x) (Ioi 0) := by
  exact (lintegral_ofReal_ne_top_iff_integrable
    (continuous_cutDispersion p hp x).aestronglyMeasurable
    (ordered_cutDispersion_ae_nonneg p hp x hx.monotone)).mp
      (ordered_lintegral_cutDispersion_ne_top p hp x hx)

theorem integral_ordered_cutDispersion_le_three_energy {n : ℕ} (p : PMF (Fin (n + 1)))
    (hp : p.support.Finite) (x : ℕ → ℝ)
    (hx : StrictMono (fun k : Fin (n + 1) ↦ x k.val)) :
    (∫ t : ℝ in Ioi 0, cutDispersion p hp x t) ≤
      3 * (VarianceEnergy.energy (p.map (fun k : Fin (n + 1) ↦ x k.val)).toMeasure).toReal := by
  let q : PMF ℝ := p.map (fun k : Fin (n + 1) ↦ x k.val)
  have hq : q.support.Finite := by simpa [q] using hp.image (fun k : Fin (n + 1) ↦ x k.val)
  have hne := finiteLaw_energy_ne_top q hq
  have hb := lintegral_cutDispersion_le_three_energy p hp x hx
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) hne) hb
  rw [integral_eq_lintegral_of_nonneg_ae (ordered_cutDispersion_ae_nonneg p hp x hx.monotone)
    (integrableOn_ordered_cutDispersion p hp x hx).aestronglyMeasurable]
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] using h

end ExactOverlaps.Poisson
