module

public import ExactOverlaps.SelfSimilar.CodingLaw
public import ExactOverlaps.SelfSimilar.BernoulliPointwise
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
Finite-prefix decompositions of the affine coding map and the almost-sure
Lyapunov contraction law along the actual Bernoulli coding orbit.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι]

noncomputable def prefixTranslation (S : System ι) (n : ℕ) (ω : ℕ → ι) : ℝ :=
  ∑ j ∈ Finset.range n, S.codingTerm j ω

theorem coding_prefix_decomposition (S : System ι) (n : ℕ) (ω : ℕ → ι) :
    S.coding ω = S.prefixTranslation n ω +
      S.prefixRatio n ω * S.coding (Bernoulli.shift^[n] ω) := by
  induction n with
  | zero => simp [prefixTranslation, prefixRatio]
  | succ n ih =>
      have htail := S.coding_shift (Bernoulli.shift^[n] ω)
      rw [Bernoulli.shift_iterate, zero_add] at htail
      have heq : Bernoulli.shift (Bernoulli.shift^[n] ω) = Bernoulli.shift^[n + 1] ω :=
        (Function.iterate_succ_apply' Bernoulli.shift n ω).symm
      rw [heq, RealSimilarity.apply_def] at htail
      rw [ih, htail, prefixRatio_succ]
      simp only [prefixTranslation, Finset.sum_range_succ, codingTerm]
      ring

theorem prefixTranslation_tendsto (S : System ι) (ω : ℕ → ι) :
    Tendsto (fun n ↦ S.prefixTranslation n ω) atTop (𝓝 (S.coding ω)) :=
  (S.summable_codingTerm ω).hasSum.tendsto_sum_nat

theorem prefixRatio_ne_zero (S : System ι) (n : ℕ) (ω : ℕ → ι) :
    S.prefixRatio n ω ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun j _ ↦ (S.map (ω j)).ratio_ne_zero)

theorem log_abs_prefixRatio (S : System ι) (n : ℕ) (ω : ℕ → ι) :
    Real.log |S.prefixRatio n ω| =
      ∑ j ∈ Finset.range n, Real.log |(S.map (ω j)).ratio| := by
  induction n with
  | zero => simp [prefixRatio]
  | succ n ih =>
      rw [prefixRatio_succ, abs_mul,
        Real.log_mul (abs_ne_zero.mpr (S.prefixRatio_ne_zero n ω))
          (abs_ne_zero.mpr (S.map (ω n)).ratio_ne_zero), ih, Finset.sum_range_succ]

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- The signed coding multiplier has the actual Lyapunov exponent almost surely. -/
theorem ae_log_abs_prefixRatio_div_tendsto (S : System ι) :
    ∀ᵐ ω ∂Bernoulli.sequenceLaw S.alphabetLaw.toMeasure,
      Tendsto (fun n : ℕ ↦ Real.log |S.prefixRatio n ω| / (n : ℝ))
        atTop (𝓝 S.lyapunov) := by
  let g : ι → ℝ := fun i ↦ Real.log |(S.map i).ratio|
  have hgm : Measurable g := measurable_of_finite _
  obtain ⟨C, hC⟩ := (Set.finite_range (fun i ↦ |g i|)).bddAbove
  have hg : Integrable g S.alphabetLaw.toMeasure := by
    apply Integrable.of_bound hgm.aestronglyMeasurable C
    exact ae_of_all _ (fun i ↦ by simpa only [Real.norm_eq_abs] using hC ⟨i, rfl⟩)
  have hhead : MeasurePreserving (fun ω : ℕ → ι ↦ ω 0)
      (Bernoulli.sequenceLaw S.alphabetLaw.toMeasure) S.alphabetLaw.toMeasure :=
    ⟨measurable_pi_apply 0, Measure.infinitePi_map_eval _ _⟩
  have hobs : Integrable (fun ω : ℕ → ι ↦ g (ω 0))
      (Bernoulli.sequenceLaw S.alphabetLaw.toMeasure) := by
    simpa only [Function.comp_def] using hhead.integrable_comp_of_integrable hg
  have hmean : (∫ ω : ℕ → ι, g (ω 0) ∂Bernoulli.sequenceLaw S.alphabetLaw.toMeasure) =
      S.lyapunov := by
    have hmmap : AEStronglyMeasurable g
        ((Bernoulli.sequenceLaw S.alphabetLaw.toMeasure).map (fun ω : ℕ → ι ↦ ω 0)) := by
      rw [hhead.map_eq]
      exact hg.aestronglyMeasurable
    rw [← integral_map (measurable_pi_apply 0).aemeasurable hmmap, hhead.map_eq,
      PMF.integral_eq_sum]
    simp only [alphabetLaw_apply, ENNReal.coe_toReal, smul_eq_mul, g, lyapunov]
  have h := Bernoulli.ae_tendsto_birkhoffAverage S.alphabetLaw.toMeasure
    (hgm.comp (measurable_pi_apply 0)) hobs
  simp only [Function.comp_def] at h
  rw [hmean] at h
  filter_upwards [h] with ω hω
  apply hω.congr
  intro n
  simp only [birkhoffAverage, smul_eq_mul, birkhoffSum, Bernoulli.shift_iterate,
    zero_add, g, log_abs_prefixRatio, div_eq_inv_mul]

end ExactOverlaps.SelfSimilar.System
