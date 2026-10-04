module

public import ExactOverlaps.SelfSimilar.AffineBoundary
public import ExactOverlaps.SelfSimilar.SimilarityLaws

/-!
Stopped cylinders for every affine image of one stationary law. All retained
cylinders have uniformly bounded rescaled ratios and lie inside whole dyadic
cells. The constants are independent of the signed affine map, provided its
magnification at the chosen level is at least one.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped Classical ENNReal BigOperators

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι]

theorem exists_stopped_affine_cylinders_in_cells (S : System ι) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] [NullSingletonClass μ] (hμ : S.IsStationary μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ ∀ g : RealSimilarity, ∀ k : ℤ,
      1 ≤ (2 : ℝ) ^ k * |g.ratio| → ∃ n : ℕ, ∃ q : Word ι n → RealSimilarity,
      ∃ G : Finset (Word ι n),
      (∀ E, MeasurableSet E → (μ.map g) E = ∑ w, S.wordWeight n w * μ ((q w) ⁻¹' E)) ∧
      (∀ w, a ≤ (2 : ℝ) ^ k * |(q w).ratio| ∧ (2 : ℝ) ^ k * |(q w).ratio| ≤ 1) ∧
      (∀ w ∈ G, ∃ j : ℤ, ∀ᵐ x ∂μ, Entropy.dyadicQuantize k (q w x) = j) ∧
      (∑ w, if w ∈ G then 0 else S.wordWeight n w) ≤ ENNReal.ofReal ε := by
  have := S.nonempty_index
  obtain ⟨ρ₀, hρ₀, hρ₀1, hboundary⟩ := S.exists_uniform_affine_boundary_bound μ hμ hε
  obtain ⟨R, hR, hfull⟩ := S.exists_closedBall_full_measure hμ
  have hsupport : ∀ᵐ x : ℝ ∂μ, |x| ≤ R := by
    have hball : ∀ᵐ x ∂μ, x ∈ closedBall (0 : ℝ) R := mem_ae_iff.mpr hfull
    simpa only [mem_closedBall, Real.dist_eq, sub_zero] using hball
  obtain ⟨a₀, ha₀, ha₀1, hmin⟩ := S.exists_min_ratio
  let ρ : ℝ := ρ₀ / 2
  have hρ : 0 < ρ := half_pos hρ₀
  have hρ1 : ρ < 1 := by dsimp [ρ]; linarith
  let a : ℝ := a₀ * ρ / (R + 1)
  have ha : 0 < a := by dsimp [a]; positivity
  refine ⟨a, ha, fun g k hs1 ↦ ?_⟩
  let s : ℝ := (2 : ℝ) ^ k * |g.ratio|
  have ht : 0 < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
  have hs : 0 < s := mul_pos ht (abs_pos.mpr g.ratio_ne_zero)
  let u : ℝ := ρ / ((R + 1) * s)
  have hu : u ∈ Ioo 0 1 := by
    constructor
    · dsimp [u]; positivity
    · dsimp [u]
      apply (div_lt_one (by positivity)).mpr
      nlinarith
  obtain ⟨n, q, hdecomp, hratio⟩ := S.exists_stopped_decomposition hμ ha₀ ha₀1 hmin hu
  let Q : Word ι n → RealSimilarity := fun w ↦ g.comp (q w)
  have hQratio (w : Word ι n) : (2 : ℝ) ^ k * |(Q w).ratio| = s * |(q w).ratio| := by
    change (2 : ℝ) ^ k * |g.ratio * (q w).ratio| = _
    rw [abs_mul]
    simp only [s, mul_assoc]
  let G : Finset (Word ι n) := Finset.univ.filter
    (fun w ↦ (2 : ℝ) ^ k * (Q w).shift ∉ integerGridNeighborhood ρ)
  have hscaled (w : Word ι n) : a ≤ s * |(q w).ratio| ∧ s * |(q w).ratio| ≤ 1 := by
    have hlow := mul_lt_mul_of_pos_left (hratio w).1 hs
    have hhigh := mul_le_mul_of_nonneg_left (hratio w).2 hs.le
    have he : s * (a₀ * u) = a := by dsimp [u, a]; field_simp
    have he' : s * u = ρ / (R + 1) := by dsimp [u]; field_simp
    rw [he] at hlow
    rw [he'] at hhigh
    refine ⟨hlow.le, hhigh.trans ?_⟩
    apply (div_le_one (by positivity)).mpr
    linarith
  have hdisp (w : Word ι n) : ∀ᵐ x ∂μ,
      |(2 : ℝ) ^ k * (Q w x) - (2 : ℝ) ^ k * (Q w).shift| ≤ ρ := by
    filter_upwards [hsupport] with x hx
    have he : (2 : ℝ) ^ k * (Q w x) - (2 : ℝ) ^ k * (Q w).shift =
        (2 : ℝ) ^ k * (Q w).ratio * x := by ring
    rw [he, abs_mul, abs_mul, abs_of_pos ht, hQratio]
    have hb := mul_le_mul_of_nonneg_left (hratio w).2 hs.le
    have hb' := mul_le_mul_of_nonneg_right hb hR.le
    have hterm : s * |(q w).ratio| * |x| ≤ s * |(q w).ratio| * R :=
      mul_le_mul_of_nonneg_left hx (mul_nonneg hs.le (abs_nonneg _))
    have hsmall : s * u * R ≤ ρ := by
      have he' : s * u * R = ρ * (R / (R + 1)) := by dsimp [u]; field_simp
      rw [he']
      have hrle : R / (R + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
      exact (mul_le_mul_of_nonneg_left hrle hρ.le).trans_eq (mul_one ρ)
    exact hterm.trans (hb'.trans hsmall)
  have hdecompQ (E : Set ℝ) (hE : MeasurableSet E) :
      (μ.map g) E = ∑ w, S.wordWeight n w * μ ((Q w) ⁻¹' E) := by
    rw [Measure.map_apply g.measurable hE, hdecomp _ (hE.preimage g.measurable)]
    apply Finset.sum_congr rfl
    intro w _
    congr 2
    ext x
    simp only [Q, mem_preimage, RealSimilarity.comp_apply]
  refine ⟨n, Q, G, hdecompQ, fun w ↦ ?_, ?_, ?_⟩
  · simpa only [hQratio] using hscaled w
  · intro w hw
    have hgood : (2 : ℝ) ^ k * (Q w).shift ∉ integerGridNeighborhood ρ := (Finset.mem_filter.mp hw).2
    refine ⟨⌊(2 : ℝ) ^ k * (Q w).shift⌋, ?_⟩
    filter_upwards [hdisp w] with x hx
    by_contra hne
    have hne' : ⌊(2 : ℝ) ^ k * (Q w).shift⌋ ≠ ⌊(2 : ℝ) ^ k * (Q w x)⌋ := by
      simpa only [Entropy.dyadicQuantize] using Ne.symm hne
    exact hgood (mem_integerGridNeighborhood_of_floor_ne (by simpa only [abs_sub_comm] using hx) hne')
  · let E : Set ℝ := (fun x : ℝ ↦ (2 : ℝ) ^ k * x) ⁻¹' integerGridNeighborhood ρ₀
    have hE : MeasurableSet E := (measurableSet_integerGridNeighborhood ρ₀).preimage
      (measurable_const.mul measurable_id)
    have hbad (w : Word ι n) (hw : w ∉ G) : μ ((Q w) ⁻¹' E) = 1 := by
      have hb : (2 : ℝ) ^ k * (Q w).shift ∈ integerGridNeighborhood ρ := by
        simpa only [G, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hw
      have hAE : ∀ᵐ x ∂μ, x ∈ (Q w) ⁻¹' E := by
        filter_upwards [hdisp w] with x hx
        have h := mem_integerGridNeighborhood_of_dist_le hb hx
        have he : ρ + ρ = ρ₀ := by dsimp [ρ]; ring
        change (2 : ℝ) ^ k * (Q w x) ∈ integerGridNeighborhood ρ₀
        simpa only [he] using h
      exact (measure_of_measure_compl_eq_zero (mem_ae_iff.mp hAE)).trans measure_univ
    calc
      _ ≤ ∑ w, S.wordWeight n w * μ ((Q w) ⁻¹' E) := by
        apply Finset.sum_le_sum
        intro w _
        split_ifs with hw
        · exact zero_le
        · rw [hbad w hw, mul_one]
      _ = (μ.map g) E := (hdecompQ E hE).symm
      _ ≤ ENNReal.ofReal ε := by
        rw [Measure.map_apply g.measurable hE]
        have hscale : 1 ≤ |(2 : ℝ) ^ k * g.ratio| := by
          simpa only [abs_mul, abs_of_pos ht] using hs1
        have hb := hboundary ((2 : ℝ) ^ k * g.ratio) hscale ((2 : ℝ) ^ k * g.shift)
        have he : g ⁻¹' E = (fun x : ℝ ↦ (2 : ℝ) ^ k * g.ratio * x +
            (2 : ℝ) ^ k * g.shift) ⁻¹' integerGridNeighborhood ρ₀ := by
          ext x
          change ((2 : ℝ) ^ k * (g.ratio * x + g.shift) ∈ integerGridNeighborhood ρ₀) ↔
            ((2 : ℝ) ^ k * g.ratio * x + (2 : ℝ) ^ k * g.shift ∈ integerGridNeighborhood ρ₀)
          simp only [mul_add, mul_assoc]
        rw [he]
        exact hb

end ExactOverlaps.SelfSimilar.System
