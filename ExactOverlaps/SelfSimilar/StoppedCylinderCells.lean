module

public import ExactOverlaps.SelfSimilar.StationaryBoundary
public import ExactOverlaps.SelfSimilar.SimilarityLaws

/-!
At every dyadic level, almost all the mass of a stopped cylinder
decomposition consists of entire cylinders carried by one cell. Their
rescaled signed ratios are uniformly bounded away from zero. The bound on
discarded weights is obtained from the actual stationary measure near grid
boundaries, so no conditional-law approximation is assumed.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped Classical ENNReal BigOperators

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι]

theorem exists_stopped_cylinders_in_cells (S : System ι) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] [NullSingletonClass μ] (hμ : S.IsStationary μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ ∀ k : ℕ, ∃ n : ℕ, ∃ q : Word ι n → RealSimilarity,
      ∃ G : Finset (Word ι n),
      (∀ E, MeasurableSet E → μ E = ∑ w, S.wordWeight n w * μ ((q w) ⁻¹' E)) ∧
      (∀ w, a ≤ (2 : ℝ) ^ k * |(q w).ratio| ∧ (2 : ℝ) ^ k * |(q w).ratio| ≤ 1) ∧
      (∀ w ∈ G, ∃ j : ℤ, ∀ᵐ x ∂μ, Entropy.dyadicQuantize k (q w x) = j) ∧
      (∑ w, if w ∈ G then 0 else S.wordWeight n w) ≤ ENNReal.ofReal ε := by
  have := S.nonempty_index
  obtain ⟨ρ₀, hρ₀, hρ₀1, hboundary⟩ := S.exists_uniform_dyadic_boundary_bound μ hμ hε
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
  refine ⟨a, ha, fun k ↦ ?_⟩
  let s : ℝ := (2 : ℝ) ^ k
  have hs : 0 < s := pow_pos (by norm_num) k
  have hs1 : 1 ≤ s := one_le_pow₀ (by norm_num)
  let u : ℝ := ρ / ((R + 1) * s)
  have hu : u ∈ Ioo 0 1 := by
    constructor
    · dsimp [u]; positivity
    · dsimp [u]
      apply (div_lt_one (by positivity)).mpr
      nlinarith
  obtain ⟨n, q, hdecomp, hratio⟩ := S.exists_stopped_decomposition hμ ha₀ ha₀1 hmin hu
  let G : Finset (Word ι n) := Finset.univ.filter
    (fun w ↦ s * (q w).shift ∉ integerGridNeighborhood ρ)
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
  have hdisp (w : Word ι n) : ∀ᵐ x ∂μ, |s * (q w x) - s * (q w).shift| ≤ ρ := by
    filter_upwards [hsupport] with x hx
    have he : s * (q w x) - s * (q w).shift = s * (q w).ratio * x := by ring
    rw [he, abs_mul, abs_mul, abs_of_pos hs]
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
  refine ⟨n, q, G, hdecomp, hscaled, ?_, ?_⟩
  · intro w hw
    have hgood : s * (q w).shift ∉ integerGridNeighborhood ρ := (Finset.mem_filter.mp hw).2
    refine ⟨⌊s * (q w).shift⌋, ?_⟩
    filter_upwards [hdisp w] with x hx
    by_contra hne
    have hne' : ⌊s * (q w).shift⌋ ≠ ⌊s * (q w x)⌋ := by
      simpa only [Entropy.dyadicQuantize, s, zpow_natCast] using Ne.symm hne
    exact hgood (mem_integerGridNeighborhood_of_floor_ne (by simpa only [abs_sub_comm] using hx) hne')
  · let E : Set ℝ := (fun x : ℝ ↦ s * x) ⁻¹' integerGridNeighborhood ρ₀
    have hE : MeasurableSet E := (measurableSet_integerGridNeighborhood ρ₀).preimage
      (measurable_const.mul measurable_id)
    have hbad (w : Word ι n) (hw : w ∉ G) : μ ((q w) ⁻¹' E) = 1 := by
      have hb : s * (q w).shift ∈ integerGridNeighborhood ρ := by
        simpa only [G, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hw
      have hAE : ∀ᵐ x ∂μ, x ∈ (q w) ⁻¹' E := by
        filter_upwards [hdisp w] with x hx
        have h := mem_integerGridNeighborhood_of_dist_le hb hx
        have he : ρ + ρ = ρ₀ := by dsimp [ρ]; ring
        change s * (q w x) ∈ integerGridNeighborhood ρ₀
        simpa only [he] using h
      exact (measure_of_measure_compl_eq_zero (mem_ae_iff.mp hAE)).trans measure_univ
    calc
      _ ≤ ∑ w, S.wordWeight n w * μ ((q w) ⁻¹' E) := by
        apply Finset.sum_le_sum
        intro w _
        split_ifs with hw
        · exact zero_le
        · rw [hbad w hw, mul_one]
      _ = μ E := (hdecomp E hE).symm
      _ ≤ ENNReal.ofReal ε := by simpa only [add_zero] using hboundary k 0

end ExactOverlaps.SelfSimilar.System
