module

public import ExactOverlaps.SelfSimilar.SimilarityLaws
public import ExactOverlaps.SelfSimilar.QuantizedCoupling

/-!
Entropy comparison under arbitrary signed affine maps. Knowing one input
cell leaves only a bounded number of output cells, uniformly in the level
and the translation. Applying the estimate to the inverse gives the lower
entropy bound needed for rescaled self-similar cylinders.
-/

@[expose] public section

open MeasureTheory Set
open scoped Classical ENNReal

namespace ExactOverlaps.Entropy

theorem fst_fiber_card_le_of_prediction (p : PMF (ℤ × ℤ))
    (hp : p.support.Finite) (F : ℤ → ℤ) {l u : ℤ}
    (hband : ∀ z ∈ p.support, z.2 - F z.1 ∈ Icc l u) (b : ℤ) :
    (hp.toFinset.filter (fun z ↦ z.1 = b)).card ≤ (u - l + 1).toNat := by
  have hsub : hp.toFinset.filter (fun z ↦ z.1 = b) ⊆
      (Finset.Icc (F b + l) (F b + u)).image (fun j ↦ (b, j)) := by
    intro z hz
    obtain ⟨hz, hzb⟩ := Finset.mem_filter.mp hz
    obtain ⟨hl, hu⟩ := hband z (by simpa using hz)
    rw [hzb] at hl hu
    refine Finset.mem_image.mpr ⟨z.2, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      constructor <;> omega
    · exact Prod.ext hzb.symm rfl
  calc
    _ ≤ ((Finset.Icc (F b + l) (F b + u)).image (fun j ↦ (b, j))).card :=
      Finset.card_le_card hsub
    _ ≤ (Finset.Icc (F b + l) (F b + u)).card := Finset.card_image_le
    _ = (u - l + 1).toNat := by rw [Int.card_Icc]; congr 1; omega

theorem dyadicEntropy_map_affine_sub_le (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (g : RealSimilarity) {K : ℕ}
    (hK : |g.ratio| ≤ K) (i : ℤ) :
    dyadicEntropy (μ.map g) (g.hasBoundedSupport_map μ hμ) i - dyadicEntropy μ hμ i ≤
      Real.log (2 * K + 3 : ℝ) := by
  let f : ℝ → ℤ := dyadicQuantize i
  let h : ℝ → ℤ := dyadicQuantize i ∘ g
  have hf : Measurable f := measurable_dyadicQuantize i
  have hh : Measurable h := (measurable_dyadicQuantize i).comp g.measurable
  let p := integerCouplingLaw μ f h
  have hμid : HasBoundedSupport (μ.map id) := by
    have he : μ.map id = μ := by
      apply ProbabilityMeasure.toMeasure_injective
      rw [ProbabilityMeasure.toMeasure_map, Measure.map_id]
    rw [he]
    exact hμ
  have hp : p.support.Finite :=
    dyadicCoupling_support_finite μ id g measurable_id g.measurable hμid
      (g.hasBoundedSupport_map μ hμ) i
  let F : ℤ → ℤ := fun k ↦ ⌊g.ratio * k + (2 : ℝ) ^ i * g.shift⌋
  have hband : ∀ z ∈ p.support, z.2 - F z.1 ∈ Icc (-(K : ℤ) - 1) ((K : ℤ) + 1) := by
    apply integerCouplingLaw_support_subset μ f h hf hh
    apply ae_of_all
    intro x
    apply floor_sub_mem_Icc_of_abs_sub_le
    have hfrac : |(2 : ℝ) ^ i * x - (⌊(2 : ℝ) ^ i * x⌋ : ℝ)| ≤ 1 := by
      rw [abs_of_nonneg (sub_nonneg.mpr (Int.floor_le _))]
      linarith [Int.lt_floor_add_one ((2 : ℝ) ^ i * x)]
    have he : (2 : ℝ) ^ i * g x -
        (g.ratio * (⌊(2 : ℝ) ^ i * x⌋ : ℝ) + (2 : ℝ) ^ i * g.shift) =
        g.ratio * ((2 : ℝ) ^ i * x - (⌊(2 : ℝ) ^ i * x⌋ : ℝ)) := by
      ring
    change |(2 : ℝ) ^ i * g x -
      (g.ratio * (⌊(2 : ℝ) ^ i * x⌋ : ℝ) + (2 : ℝ) ^ i * g.shift)| ≤ K
    rw [he, abs_mul]
    calc
      _ ≤ |g.ratio| * 1 := mul_le_mul_of_nonneg_left hfrac (abs_nonneg g.ratio)
      _ ≤ K := by simpa using hK
  have hb : finiteEntropy (p.map Prod.snd) (by simpa using hp.image Prod.snd) -
      finiteEntropy (p.map Prod.fst) (by simpa using hp.image Prod.fst) ≤
        Real.log (((K : ℤ) + 1 - (-(K : ℤ) - 1) + 1).toNat) := by
    apply entropy_map_sub_le_log_of_fiber_card_le p hp Prod.fst Prod.snd
    intro b
    convert fst_fiber_card_le_of_prediction p hp F hband b using 1
    congr 1
    ext z
    simp only [Finset.mem_filter]
  have hfst : p.map Prod.fst = dyadicLaw μ i := integerCouplingLaw_map_fst μ f h hf hh
  have hsnd : p.map Prod.snd = dyadicLaw (μ.map g) i :=
    (integerCouplingLaw_map_snd μ f h hf hh).trans (dyadicLaw_map μ g g.measurable i).symm
  have hcount : ((((K : ℤ) + 1 - (-(K : ℤ) - 1) + 1).toNat) : ℝ) = 2 * K + 3 := by
    have he : (K : ℤ) + 1 - (-(K : ℤ) - 1) + 1 = ((2 * K + 3 : ℕ) : ℤ) := by omega
    rw [he, Int.toNat_natCast]
    push_cast
    rfl
  simpa only [hfst, hsnd, hcount, dyadicEntropy] using hb

theorem dyadicEntropy_le_map_affine_add (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (g : RealSimilarity) {K : ℕ}
    (hK : |g.ratio|⁻¹ ≤ K) (i : ℤ) :
    dyadicEntropy μ hμ i ≤
      dyadicEntropy (μ.map g) (g.hasBoundedSupport_map μ hμ) i + Real.log (2 * K + 3 : ℝ) := by
  have hratio : |g.inverse.ratio| ≤ K := by simpa only [RealSimilarity.inverse, abs_inv] using hK
  have h := dyadicEntropy_map_affine_sub_le (μ.map g) (g.hasBoundedSupport_map μ hμ)
    g.inverse hratio i
  simp only [g.probability_map_inverse μ] at h
  linarith

end ExactOverlaps.Entropy
