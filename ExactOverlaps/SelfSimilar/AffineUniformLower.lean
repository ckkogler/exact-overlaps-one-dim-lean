module

public import ExactOverlaps.SelfSimilar.DyadicCellMixtureTail
public import ExactOverlaps.SelfSimilar.StoppedAffineCylinderCells
public import ExactOverlaps.SelfSimilar.AffineEntropyScale
public import ExactOverlaps.SelfSimilar.UniformSelfSimilar

/-!
Uniform lower entropy tails for all affine images of one stationary law.
The window length is independent of the affine ratio and translation;
only the observation level must resolve the affine image at unit scale.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology Classical ENNReal BigOperators

namespace ExactOverlaps.Entropy

theorem uniform_affine_entropy_lower_bound_int (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) {d a : ℝ}
    (hlim : Tendsto (normalizedDyadicEntropy μ hμ) atTop (𝓝 d)) (ha : 0 < a)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → 0 < m → ∀ k : ℤ, ∀ g : RealSimilarity,
      a ≤ (2 : ℝ) ^ k * |g.ratio| →
      (d - δ) * ((m : ℝ) * Real.log 2) ≤
        dyadicEntropy (μ.map g) (g.hasBoundedSupport_map μ hμ) (k + m) := by
  obtain ⟨M, hM⟩ := uniform_affine_entropy_lower_bound μ hμ hlim ha hδ
  refine ⟨M, fun m hm hmpos k g hr ↦ ?_⟩
  have hg : a ≤ (2 : ℝ) ^ (0 : ℕ) * |(g.dyadicScale k).ratio| := by
    simpa only [RealSimilarity.dyadicScale, pow_zero, one_mul, abs_mul,
      abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) k)] using hr
  have h := hM m hm hmpos 0 (g.dyadicScale k) hg
  simpa only [Nat.cast_zero, zero_add, dyadicEntropy_affine_scale μ hμ g k m] using h

end ExactOverlaps.Entropy

namespace ExactOverlaps.SelfSimilar.System

open Entropy
variable {ι : Type*} [Fintype ι]

theorem uniform_affine_entropy_lower_tail (S : System ι) (μ : ProbabilityMeasure ℝ)
    [NullSingletonClass (μ : Measure ℝ)] (hμ : S.IsStationary (μ : Measure ℝ))
    {d : ℝ} (hd : d ≤ 1)
    (hlim : Tendsto (normalizedDyadicEntropy μ (S.hasBoundedSupport hμ)) atTop (𝓝 d))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → 0 < m → ∀ g : RealSimilarity, ∀ i : ℤ,
      1 ≤ (2 : ℝ) ^ i * |g.ratio| →
      componentEntropyBelowMass (μ.map g) (g.hasBoundedSupport_map μ (S.hasBoundedSupport hμ))
        i m d δ ≤ δ := by
  by_cases hA : 0 ≤ d - δ / 2
  swap
  · refine ⟨0, fun m _ _ g i _ ↦ ?_⟩
    rw [componentEntropyBelowMass_eq_zero_of_lt (μ.map g) _ i m (by linarith : d < δ)]
    exact hδ.le
  let ε : ℝ := δ * δ / 4
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨a, ha, hstopped⟩ := S.exists_stopped_affine_cylinders_in_cells (μ : Measure ℝ) hμ hε
  obtain ⟨M, hM⟩ := uniform_affine_entropy_lower_bound_int μ (S.hasBoundedSupport hμ)
    hlim ha (half_pos hδ)
  refine ⟨M, fun m hm hmpos g i hscale ↦ ?_⟩
  obtain ⟨n, q, G, hdecomp, hratio, hgood, hbad⟩ := hstopped g i hscale
  let ν : Word ι n → ProbabilityMeasure ℝ := fun w ↦ μ.map (q w)
  let hν : ∀ w, HasBoundedSupport (ν w) := fun w ↦ (q w).hasBoundedSupport_map μ (S.hasBoundedSupport hμ)
  have hmix : (μ.map g : Measure ℝ) = ∑ w, S.wordLaw n w • (ν w : Measure ℝ) := by
    apply Measure.ext
    intro E hE
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul, ν,
      ProbabilityMeasure.toMeasure_map, wordLaw_apply, Measure.map_apply (q _).measurable hE]
    exact hdecomp E hE
  have hwhole : ∀ w ∈ G, (∃ k : ℤ, ∀ᵐ x ∂(ν w : Measure ℝ), dyadicQuantize i x = k) ∧
      (d - δ / 2) * ((m : ℝ) * Real.log 2) ≤ dyadicEntropy (ν w) (hν w) (i + m) := by
    intro w hw
    obtain ⟨k, hk⟩ := hgood w hw
    constructor
    · refine ⟨k, ?_⟩
      change ∀ᵐ x ∂((μ : Measure ℝ).map (q w)), dyadicQuantize i x = k
      apply (ae_map_iff (q w).measurable.aemeasurable
        ((measurable_dyadicQuantize i) (measurableSet_singleton k))).mpr
      exact hk
    · exact hM m hm hmpos i (q w) (hratio w).1
  have hbadreal : (∑ w, if w ∈ G then 0 else (S.wordLaw n w).toReal) ≤ ε := by
    have h := ENNReal.toReal_le_of_le_ofReal hε.le hbad
    rw [ENNReal.toReal_sum] at h
    · simpa only [wordLaw_apply, ENNReal.toReal_zero, apply_ite ENNReal.toReal] using h
    · intro w _
      split_ifs
      · exact ENNReal.zero_ne_top
      · exact (S.wordLaw n).apply_ne_top w
  have htail := dyadic_mixture_below_mass_le (S.wordLaw n) ν hν (μ.map g)
    (g.hasBoundedSupport_map μ (S.hasBoundedSupport hμ))
    hmix i hmpos G hA hwhole
  have hprod : (d - δ / 2) * (∑ w, if w ∈ G then 0 else (S.wordLaw n w).toReal) ≤ ε := by
    calc
      _ ≤ (d - δ / 2) * ε := mul_le_mul_of_nonneg_left hbadreal hA
      _ ≤ 1 * ε := mul_le_mul_of_nonneg_right (by linarith) hε.le
      _ = ε := one_mul ε
  have hbound : (δ / 2) * componentEntropyBelowMass (μ.map g) (g.hasBoundedSupport_map μ (S.hasBoundedSupport hμ)) i m d δ ≤
      δ * δ / 4 := htail.trans hprod
  apply (mul_le_mul_iff_right₀ (half_pos hδ)).mp
  nlinarith only [hbound, sq_nonneg δ]

end ExactOverlaps.SelfSimilar.System
