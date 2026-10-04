module

public import ExactOverlaps.SelfSimilar.AffineEntropyDeficit
public import ExactOverlaps.Entropy.SufficientInverse

/-!
A fixed entropy gain for convolving any normalized affine copy of a
self-similar measure of dimension below one with a positive-entropy law.
Both the gain and eventual threshold are uniform over a compact range of
absolute affine ratios and over arbitrary translations.
-/

@[expose] public section

open MeasureTheory Filter Set

namespace ExactOverlaps.SelfSimilar.System

open Entropy
variable {ι : Type*} [Fintype ι]

theorem exists_uniform_affine_inverse (S : System ι) (μ : ProbabilityMeasure ℝ)
    (hμ : S.IsStationary (μ : Measure ℝ))
    (hdim : (lowerHausdorffDimension (μ : Measure ℝ)).toReal < 1)
    {a e : ℝ} (ha : 0 < a) (K : ℕ) (he : 0 < e) :
    ∃ γ > 0, ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ∀ (g : RealSimilarity) (ν : ProbabilityMeasure ℝ) (hν : HasBoundedSupport ν),
      a ≤ |g.ratio| → |g.ratio| ≤ K →
      (∀ᵐ x ∂(μ.map g : Measure ℝ), x ∈ Icc (0 : ℝ) 1) →
      (∀ᵐ x ∂(ν : Measure ℝ), x ∈ Icc (0 : ℝ) 1) →
      e < normalizedDyadicEntropy ν hν n →
      normalizedDyadicEntropy (μ.map g) (g.hasBoundedSupport_map μ (S.hasBoundedSupport hμ)) n + γ ≤
        normalizedDyadicEntropy (realConvolution (μ.map g) ν)
          (realConvolution_hasBoundedSupport _ _
            (g.hasBoundedSupport_map μ (S.hasBoundedSupport hμ)) hν) n := by
  let d : ℝ := (lowerHausdorffDimension (μ : Measure ℝ)).toReal
  let b : ℝ := (1 - d) / 2
  have hb : 0 < b := by dsimp [b, d]; linarith
  have hgap : (lowerHausdorffDimension (μ : Measure ℝ)).toReal < 1 - b := by
    dsimp [b, d]
    linarith
  obtain ⟨M₀, hM₀, hinverse⟩ := exists_sufficient_inverse_entropy hb he
  obtain ⟨M₁, hdeficit⟩ := S.uniform_affine_entropy_deficit μ hμ ha K hgap
    (show 0 < e / 32 by positivity)
  let m := max M₀ M₁
  have hm : 0 < m := lt_of_lt_of_le hM₀ (le_max_left _ _)
  obtain ⟨γ, hγ, N₀, hN₀, hgain⟩ := hinverse m (le_max_left _ _)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (hdeficit m (le_max_right _ _) hm)
  refine ⟨γ, hγ, max N₀ N₁, lt_of_lt_of_le hN₀ (le_max_left _ _), ?_⟩
  intro n hn g ν hν hga hgK hunit hνunit hent
  have hn₀ : N₀ ≤ n := (le_max_left _ _).trans hn
  have hn₁ : N₁ ≤ n := (le_max_right _ _).trans hn
  exact hgain n hn₀ (μ.map g) ν (g.hasBoundedSupport_map μ (S.hasBoundedSupport hμ)) hν
    hunit hνunit (hN₁ n hn₁ g hga hgK) hent

end ExactOverlaps.SelfSimilar.System
