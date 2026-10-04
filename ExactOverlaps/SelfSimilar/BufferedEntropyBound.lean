module

public import ExactOverlaps.SelfSimilar.ClampedRatioComponents

/-!
An explicit eventual upper bound for the translation entropy increment.
It separates label entropy, exceptional ratio mass, the stationary-versus-tail
entropy residual, and the cost of moving component levels to the common buffer.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology BigOperators

namespace ExactOverlaps.SelfSimilar.System

open Entropy
variable {ι : Type*} [Fintype ι]

noncomputable def translationEntropyIncrement (S : System ι) (n : ℕ) (i f : ℤ) : ℝ :=
  dyadicEntropy (S.wordTranslationProbability n) (S.wordTranslationProbability_hasBoundedSupport n) f -
    dyadicEntropy (S.wordTranslationProbability n) (S.wordTranslationProbability_hasBoundedSupport n) i

noncomputable def stationaryTailEntropyResidual (S : System ι)
    (μ : ProbabilityMeasure ℝ) (hμ : S.IsStationary (μ : Measure ℝ)) (n : ℕ) (i f : ℤ) : ℝ :=
  dyadicEntropy μ (S.hasBoundedSupport hμ) f - dyadicEntropy μ (S.hasBoundedSupport hμ) i -
    S.averageRatioScaledEntropy μ (S.hasBoundedSupport hμ) n f +
    S.averageRatioScaledEntropy μ (S.hasBoundedSupport hμ) n i

noncomputable def bufferedEntropyUpper (S : System ι)
    (μ : ProbabilityMeasure ℝ) (hμ : S.IsStationary (μ : Measure ℝ))
    (e γ ε q : ℝ) (n : ℕ) : ℝ :=
  let i := bufferedRatioLevel S.dyadicLyapunov ε n
  let f := targetRatioLevel S.dyadicLyapunov q n
  let B := S.ratioClassBadMass n (S.typicalRatioClasses ε n)
  let D : ℝ := ((f - i : ℤ) : ℝ)
  finiteEntropy (S.wordRatioLaw n) (S.wordRatioLaw_support_finite n) +
    (e + B) * (D * Real.log 2) +
    (S.stationaryTailEntropyResidual μ hμ n i f + 2 * Real.log 2) / γ +
    (3 * ε * n + 1 + D * B) * Real.log 2

theorem exists_eventual_buffered_translation_bound (S : System ι)
    (μ : ProbabilityMeasure ℝ) (hμ : S.IsStationary (μ : Measure ℝ))
    (hdim : (lowerHausdorffDimension (μ : Measure ℝ)).toReal < 1) {e : ℝ} (he : 0 < e) :
    ∃ γ > 0, ∀ ε q : ℝ, 0 < ε → 1 < q → 0 < (q - 1) * S.dyadicLyapunov - ε →
      ∀ᶠ n : ℕ in atTop,
        S.translationEntropyIncrement n (bufferedRatioLevel S.dyadicLyapunov ε n)
          (targetRatioLevel S.dyadicLyapunov q n) ≤ S.bufferedEntropyUpper μ hμ e γ ε q n := by
  obtain ⟨γ, hγ, N, _, hmaster⟩ := S.exists_ratio_component_entropy_bound μ hμ hdim he
  refine ⟨γ, hγ, ?_⟩
  intro ε q hε hq hgap
  filter_upwards [S.eventually_typical_component_levels hε hgap N,
    S.eventually_averageRatioLevelGap_le hε hq hgap] with n hn hgapmean
  let i := bufferedRatioLevel S.dyadicLyapunov ε n
  let f := targetRatioLevel S.dyadicLyapunov q n
  let j := S.ratioComponentLevel ε q n
  let G := S.typicalRatioClasses ε n
  let B := S.ratioClassBadMass n G
  let D : ℝ := ((f - i : ℤ) : ℝ)
  have hif : i ≤ f := bufferedRatioLevel_le_target S.dyadicLyapunov_pos.le hε.le hq.le n
  have hij (r : (S.wordRatioLaw n).support) : i ≤ j r := le_clampLevel _ _ _
  have hjf (r : (S.wordRatioLaw n).support) : j r ≤ f := clampLevel_le hif _
  have hgood : ∀ r ∈ G, N ≤ (f - j r).toNat ∧
      (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (j r) * |(r : ℝ)| ∧ (2 : ℝ) ^ (j r) * |(r : ℝ)| ≤ 1 := by
    intro r hr
    obtain ⟨heq, hN⟩ := hn r hr
    refine ⟨hN, ?_, ?_⟩
    · change (1 / 2 : ℝ) ≤ (2 : ℝ) ^ S.ratioComponentLevel ε q n r * |(r : ℝ)|
      rw [heq]
      exact (half_lt_ratioLevel_mul (S.wordRatioLaw_support_ne_zero n r)).le
    · change (2 : ℝ) ^ S.ratioComponentLevel ε q n r * |(r : ℝ)| ≤ 1
      rw [heq]
      exact ratioLevel_mul_le_one (S.wordRatioLaw_support_ne_zero n r)
  have hm := hmaster n j i f hif hij hjf G hgood
  have hA : S.averageVariableRatioTranslationEntropy n j f ≤
      (e + B) * (D * Real.log 2) +
        (S.stationaryTailEntropyResidual μ hμ n i f + 2 * Real.log 2) / γ := by
    have heq : γ * ((S.stationaryTailEntropyResidual μ hμ n i f + 2 * Real.log 2) / γ) =
        S.stationaryTailEntropyResidual μ hμ n i f + 2 * Real.log 2 := by
      field_simp
    dsimp [stationaryTailEntropyResidual] at heq ⊢
    nlinarith [hm]
  have ht := S.translation_increment_le_variable_components_add_gap n j hif hij hjf
  let : Fintype (S.wordRatioLaw n).support := (S.wordRatioLaw_support_finite n).fintype
  have hgapEq : (∑ r : (S.wordRatioLaw n).support,
      (S.wordRatioLaw n r).toReal * ((j r - i : ℤ) : ℝ) * Real.log 2) =
      S.averageRatioLevelGap n j i * Real.log 2 := by
    unfold averageRatioLevelGap
    exact (Finset.sum_mul _ _ _).symm
  rw [hgapEq] at ht
  have hgapBound := mul_le_mul_of_nonneg_right hgapmean (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  change S.translationEntropyIncrement n i f ≤ _ at ht
  change S.translationEntropyIncrement n i f ≤
    finiteEntropy (S.wordRatioLaw n) (S.wordRatioLaw_support_finite n) +
      (e + B) * (D * Real.log 2) +
      (S.stationaryTailEntropyResidual μ hμ n i f + 2 * Real.log 2) / γ +
      (3 * ε * n + 1 + D * B) * Real.log 2
  linarith

end ExactOverlaps.SelfSimilar.System
