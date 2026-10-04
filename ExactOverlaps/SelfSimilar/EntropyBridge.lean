module

public import ExactOverlaps.SelfSimilar.CompactSupport
public import ExactOverlaps.SelfSimilar.RatioCounts
public import ExactOverlaps.Entropy.Dyadic
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
Elementary bridges from genuine stationary systems to the entropy interfaces.
The signed contraction class has sublinear entropy because its support is
polynomially bounded. No entropy-dimension or inverse theorem is assumed.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι]

theorem hasBoundedSupport (S : System ι) {ν : ProbabilityMeasure ℝ}
    (hν : S.IsStationary (ν : Measure ℝ)) : Entropy.HasBoundedSupport ν := by
  obtain ⟨R, _, hR⟩ := S.exists_closedBall_full_measure hν
  refine ⟨-R, R, ?_⟩
  have hball : ∀ᵐ x ∂(ν : Measure ℝ), x ∈ Metric.closedBall (0 : ℝ) R :=
    ae_iff.mpr hR
  filter_upwards [hball] with x hx
  simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le, mem_Icc] using hx

/-- The law of the signed linear part of the random composition. -/
noncomputable def wordRatioLaw (S : System ι) (n : ℕ) : PMF ℝ :=
  (S.wordLaw n).map (S.wordRatio n)

theorem wordRatioLaw_support_finite (S : System ι) (n : ℕ) :
    (S.wordRatioLaw n).support.Finite := by
  rw [wordRatioLaw, PMF.support_map]
  exact (Set.toFinite _).image _

theorem wordRatioLaw_support_card_le (S : System ι) (n : ℕ) :
    (S.wordRatioLaw_support_finite n).toFinset.card ≤ (n + 1) ^ Fintype.card ι := by
  classical
  apply le_trans (Finset.card_le_card (t := Finset.univ.image (S.wordRatio n)) ?_)
    (S.card_wordRatios_le n)
  intro r hr
  have hr' : r ∈ (S.wordRatioLaw n).support := by simpa using hr
  obtain ⟨w, _, hw⟩ := (PMF.mem_support_map_iff _ _ _).mp hr'
  exact Finset.mem_image.mpr ⟨w, Finset.mem_univ _, hw⟩

theorem wordRatioLaw_entropy_le (S : System ι) (n : ℕ) :
    Entropy.finiteEntropy (S.wordRatioLaw n) (S.wordRatioLaw_support_finite n) ≤
      (Fintype.card ι : ℝ) * Real.log (n + 1 : ℝ) := by
  have hcard := S.wordRatioLaw_support_card_le n
  have hpos : (0 : ℝ) < (S.wordRatioLaw_support_finite n).toFinset.card := by
    exact_mod_cast Finset.card_pos.mpr (by simp)
  calc
    Entropy.finiteEntropy (S.wordRatioLaw n) (S.wordRatioLaw_support_finite n) ≤
        Real.log (S.wordRatioLaw_support_finite n).toFinset.card :=
      Entropy.finiteEntropy_le_log_card _ _
    _ ≤ Real.log (((n + 1) ^ Fintype.card ι : ℕ) : ℝ) :=
      Real.log_le_log hpos (by exact_mod_cast hcard)
    _ = (Fintype.card ι : ℝ) * Real.log (n + 1 : ℝ) := by
      rw [Nat.cast_pow, Nat.cast_add, Nat.cast_one, Real.log_pow]

theorem tendsto_log_nat_add_one_div :
    Tendsto (fun n : ℕ ↦ Real.log (n + 1 : ℝ) / n) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n + 1 : ℝ) / (n + 1 : ℝ))
      atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hratio : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) / n) atTop (𝓝 1) := by
    simpa [add_comm] using tendsto_add_mul_div_add_mul_atTop_nhds (𝕜 := ℝ)
      1 0 1 (d := 1) one_ne_zero
  have he (n : ℕ) : Real.log (n + 1 : ℝ) / (n + 1 : ℝ) * (((n : ℝ) + 1) / n) =
      Real.log (n + 1 : ℝ) / n := by
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  simpa only [he, zero_mul] using hlog.mul hratio

/-- Recording the signed contraction has vanishing entropy per letter. -/
theorem wordRatioLaw_entropy_div_tendsto_zero (S : System ι) :
    Tendsto (fun n : ℕ ↦
      Entropy.finiteEntropy (S.wordRatioLaw n) (S.wordRatioLaw_support_finite n) / n)
      atTop (𝓝 0) := by
  have hupper : Tendsto (fun n : ℕ ↦
      (Fintype.card ι : ℝ) * Real.log (n + 1 : ℝ) / n) atTop (𝓝 0) := by
    simpa only [mul_div_assoc, mul_zero] using
      tendsto_log_nat_add_one_div.const_mul (Fintype.card ι : ℝ)
  apply squeeze_zero (fun n ↦ div_nonneg (Entropy.finiteEntropy_nonneg _ _) (Nat.cast_nonneg n))
    (fun n ↦ div_le_div_of_nonneg_right (S.wordRatioLaw_entropy_le n) (Nat.cast_nonneg n)) hupper

end ExactOverlaps.SelfSimilar.System
