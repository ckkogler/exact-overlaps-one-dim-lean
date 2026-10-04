module

public import ExactOverlaps.SelfSimilar.DimensionIdentification
public import ExactOverlaps.SelfSimilar.RatioLevelWindows

/-!
Entropy along linearly growing integer levels. The result uses the genuine
entropy-dimension limit and retains the conversion from dyadic to natural units.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace ExactOverlaps.Entropy

theorem int_level_tendsto_atTop_of_div_tendsto {j : ℕ → ℤ} {c : ℝ}
    (hc : 0 < c) (hj : Tendsto (fun n : ℕ ↦ (j n : ℝ) / n) atTop (𝓝 c)) :
    Tendsto j atTop atTop := by
  apply tendsto_atTop.2
  intro b
  have hnear : ∀ᶠ n : ℕ in atTop, c / 2 < (j n : ℝ) / n :=
    hj.eventually (lt_mem_nhds (by linarith))
  have hlarge : ∀ᶠ n : ℕ in atTop, (b : ℝ) / (c / 2) ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hnear, hlarge, eventually_gt_atTop 0] with n hn hbn hnpos
  have hn' : (0 : ℝ) < n := by exact_mod_cast hnpos
  have h₁ := (lt_div_iff₀ hn').mp hn
  have h₂ := (div_le_iff₀ (show 0 < c / 2 by positivity)).mp hbn
  exact_mod_cast (show (b : ℝ) ≤ (j n : ℝ) by nlinarith)

theorem dyadicEntropy_level_div_tendsto (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) {d c : ℝ} {j : ℕ → ℤ}
    (hlim : Tendsto (normalizedDyadicEntropy μ hμ) atTop (𝓝 d))
    (hc : 0 < c) (hj : Tendsto (fun n : ℕ ↦ (j n : ℝ) / n) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ ↦ dyadicEntropy μ hμ (j n) / n) atTop (𝓝 (d * c * Real.log 2)) := by
  have hjtop := int_level_tendsto_atTop_of_div_tendsto hc hj
  have hnat : Tendsto (fun n ↦ (j n).toNat) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hjtop.eventually (eventually_ge_atTop (b : ℤ))] with n hn
    omega
  have h := ((hlim.comp hnat).mul hj).mul_const (Real.log 2)
  apply h.congr'
  filter_upwards [hjtop.eventually (eventually_gt_atTop 0)] with n hn
  have hnj : (j n).toNat ≠ 0 := by omega
  have hjcast : ((j n).toNat : ℤ) = j n := Int.toNat_of_nonneg hn.le
  have hden : ((j n).toNat : ℝ) * Real.log 2 ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr hnj) (Real.log_pos (by norm_num)).ne'
  have hjreal : ((j n).toNat : ℝ) = (j n : ℝ) := by exact_mod_cast hjcast
  change normalizedDyadicEntropy μ hμ (j n).toNat * ((j n : ℝ) / n) * Real.log 2 =
    dyadicEntropy μ hμ (j n) / n
  simp only [normalizedDyadicEntropy, hjcast]
  rw [← hjreal]
  field_simp [Nat.cast_ne_zero.mpr hnj, (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']

end ExactOverlaps.Entropy

namespace ExactOverlaps.SelfSimilar.System

open Entropy
variable {ι : Type*} [Fintype ι]

theorem dyadicEntropy_level_div_tendsto_dimension (S : System ι)
    (μ : ProbabilityMeasure ℝ) (hμ : S.IsStationary (μ : Measure ℝ))
    {c : ℝ} {j : ℕ → ℤ} (hc : 0 < c)
    (hj : Tendsto (fun n : ℕ ↦ (j n : ℝ) / n) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ ↦ dyadicEntropy μ (S.hasBoundedSupport hμ) (j n) / n)
      atTop (𝓝 ((lowerHausdorffDimension (μ : Measure ℝ)).toReal * c * Real.log 2)) :=
  dyadicEntropy_level_div_tendsto μ (S.hasBoundedSupport hμ)
    (S.normalizedDyadicEntropy_tendsto_dimension μ hμ) hc hj

end ExactOverlaps.SelfSimilar.System
