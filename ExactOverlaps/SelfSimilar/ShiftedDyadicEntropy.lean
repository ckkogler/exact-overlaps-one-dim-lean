module

public import ExactOverlaps.SelfSimilar.DyadicStability

/-!
A grid translation changes the entropy by at most log 2. The argument uses
the actual joint law of the two cell labels and applies to every bounded
Borel probability measure, including measures charging grid boundaries.
-/

@[expose] public section

open MeasureTheory Set
open scoped Classical ENNReal

namespace ExactOverlaps.Entropy

noncomputable def shiftedDyadicQuantize (i : ℤ) (t x : ℝ) : ℤ :=
  ⌊(2 : ℝ) ^ i * x + t⌋

@[fun_prop] theorem measurable_shiftedDyadicQuantize (i : ℤ) (t : ℝ) :
    Measurable (shiftedDyadicQuantize i t) := by
  unfold shiftedDyadicQuantize
  fun_prop

theorem shiftedDyadicQuantize_sub_mem_Icc (i : ℤ) (t x : ℝ) :
    shiftedDyadicQuantize i t x - dyadicQuantize i x ∈ Icc ⌊t⌋ (⌊t⌋ + 1) := by
  have hl := Int.le_floor_add ((2 : ℝ) ^ i * x) t
  have hu := Int.le_floor_add_floor ((2 : ℝ) ^ i * x) t
  change ⌊(2 : ℝ) ^ i * x + t⌋ - ⌊(2 : ℝ) ^ i * x⌋ ∈ Icc ⌊t⌋ (⌊t⌋ + 1)
  constructor <;> omega

noncomputable def shiftedDyadicLaw (μ : ProbabilityMeasure ℝ) (i : ℤ) (t : ℝ) : PMF ℤ :=
  (μ.map (shiftedDyadicQuantize i t)).toMeasure.toPMF

theorem dyadicShiftCoupling_support_finite (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) (t : ℝ) :
    (integerCouplingLaw μ (dyadicQuantize i) (shiftedDyadicQuantize i t)).support.Finite := by
  obtain ⟨a, b, hab⟩ := hμ
  apply integerCouplingLaw_support_finite μ _ _ (measurable_dyadicQuantize i)
    (measurable_shiftedDyadicQuantize i t)
    (Set.finite_Icc (dyadicQuantize i a) (dyadicQuantize i b))
    (Set.finite_Icc (shiftedDyadicQuantize i t a) (shiftedDyadicQuantize i t b))
  filter_upwards [hab] with x hx
  have hl := mul_le_mul_of_nonneg_left hx.1 (dyadic_scale_pos i).le
  have hu := mul_le_mul_of_nonneg_left hx.2 (dyadic_scale_pos i).le
  exact ⟨⟨Int.floor_mono hl, Int.floor_mono hu⟩,
    ⟨Int.floor_mono (add_le_add hl le_rfl), Int.floor_mono (add_le_add hu le_rfl)⟩⟩

theorem shiftedDyadicLaw_support_finite (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) (t : ℝ) :
    (shiftedDyadicLaw μ i t).support.Finite := by
  have h := (dyadicShiftCoupling_support_finite μ hμ i t).image Prod.snd
  rw [← PMF.support_map, integerCouplingLaw_map_snd μ _ _
    (measurable_dyadicQuantize i) (measurable_shiftedDyadicQuantize i t)] at h
  exact h

noncomputable def shiftedDyadicEntropy (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) (t : ℝ) : ℝ :=
  finiteEntropy (shiftedDyadicLaw μ i t) (shiftedDyadicLaw_support_finite μ hμ i t)

/-- A sharp mesh-independent comparison for arbitrary grid shifts. -/
theorem abs_shiftedDyadicEntropy_sub_le_log_two (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) (t : ℝ) :
    |shiftedDyadicEntropy μ hμ i t - dyadicEntropy μ hμ i| ≤ Real.log 2 := by
  let p := integerCouplingLaw μ (dyadicQuantize i) (shiftedDyadicQuantize i t)
  have hp : p.support.Finite := dyadicShiftCoupling_support_finite μ hμ i t
  have hband : ∀ z ∈ p.support, z.2 - z.1 ∈ Icc ⌊t⌋ (⌊t⌋ + 1) := by
    apply integerCouplingLaw_support_subset μ _ _ (measurable_dyadicQuantize i)
      (measurable_shiftedDyadicQuantize i t)
    exact ae_of_all _ (fun x ↦ shiftedDyadicQuantize_sub_mem_Icc i t x)
  have h := abs_snd_entropy_sub_fst_le_of_sub_mem_Icc p hp hband
  have hfst : p.map Prod.fst = dyadicLaw μ i :=
    integerCouplingLaw_map_fst μ _ _ (measurable_dyadicQuantize i)
      (measurable_shiftedDyadicQuantize i t)
  have hsnd : p.map Prod.snd = shiftedDyadicLaw μ i t :=
    integerCouplingLaw_map_snd μ _ _ (measurable_dyadicQuantize i)
      (measurable_shiftedDyadicQuantize i t)
  have htwo : ⌊t⌋ + 1 - ⌊t⌋ + 1 = (2 : ℤ) := by omega
  simpa [hfst, hsnd, htwo, shiftedDyadicEntropy, dyadicEntropy] using h

end ExactOverlaps.Entropy
