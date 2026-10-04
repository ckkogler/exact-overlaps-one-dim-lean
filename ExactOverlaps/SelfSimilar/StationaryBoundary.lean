module

public import ExactOverlaps.SelfSimilar.GridBoundary
public import ExactOverlaps.SelfSimilar.StoppingWords
public import ExactOverlaps.SelfSimilar.CompactSupport

/-!
An atomless stationary law puts uniformly small mass near every translated
dyadic grid boundary. First-crossing words normalize every grid mesh to
affine ratios bounded above and away from zero, including negative ratios.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped ENNReal NNReal BigOperators

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι]

theorem exists_uniform_dyadic_boundary_bound (S : System ι) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] [NullSingletonClass μ] (hμ : S.IsStationary μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ k : ℕ, ∀ t : ℝ,
      μ ((fun x : ℝ ↦ (2 : ℝ) ^ k * x + t) ⁻¹' integerGridNeighborhood ρ) ≤
        ENNReal.ofReal ε := by
  classical
  have := S.nonempty_index
  obtain ⟨R, hR, hfull⟩ := S.exists_closedBall_full_measure hμ
  obtain ⟨N, hN⟩ := exists_nat_ge (R + 2)
  have hsupport : ∀ᵐ x : ℝ ∂μ, |x| + 2 ≤ (N : ℝ) := by
    have hball : ∀ᵐ x ∂μ, x ∈ closedBall (0 : ℝ) R := mem_ae_iff.mpr hfull
    filter_upwards [hball] with x hx
    have hx' : |x| ≤ R := by simpa only [mem_closedBall, Real.dist_eq, sub_zero] using hx
    linarith
  let η : ℝ := ε / (2 * N + 1)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨δ, hδ, hsmall⟩ := exists_uniform_closedBall_measure_lt μ
    (isCompact_closedBall (0 : ℝ) R) hfull (ENNReal.ofReal_pos.mpr hη)
  obtain ⟨a, ha, ha1, hmin⟩ := S.exists_min_ratio
  let ρ : ℝ := min (1 / 2) (a * δ / 2)
  have hρ : 0 < ρ := lt_min (by norm_num) (by positivity)
  have hρ1 : ρ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hscale : ρ ≤ (a / 2) * δ := by
    have h := min_le_right (1 / 2 : ℝ) (a * δ / 2)
    dsimp [ρ]
    nlinarith
  have hmass : (2 * N + 1 : ℕ) * ENNReal.ofReal η = ENNReal.ofReal ε := by
    have hpos : (0 : ℝ) < 2 * N + 1 := by positivity
    have he : (2 * N + 1 : ℝ) * η = ε := by
      dsimp [η]
      field_simp
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using
      congrArg ENNReal.ofReal he
  refine ⟨ρ, hρ, hρ1, fun k t ↦ ?_⟩
  let s : ℝ := (2 : ℝ) ^ k
  have hs : 0 < s := pow_pos (by norm_num) k
  have hs1 : 1 ≤ s := one_le_pow₀ (by norm_num)
  let u : ℝ := 1 / (2 * s)
  have hu : u ∈ Ioo 0 1 := by
    constructor
    · dsimp [u]; positivity
    · dsimp [u]
      apply (div_lt_one (by positivity)).mpr
      linarith
  obtain ⟨n, q, hdecomp, hratio⟩ := S.exists_stopped_decomposition hμ ha ha1 hmin hu
  let E : Set ℝ := (fun x : ℝ ↦ s * x + t) ⁻¹' integerGridNeighborhood ρ
  have hE : MeasurableSet E := (measurableSet_integerGridNeighborhood ρ).preimage
    ((measurable_const.mul measurable_id).add measurable_const)
  change μ E ≤ _
  rw [hdecomp E hE]
  have hbranch (w : Word ι n) : μ ((q w) ⁻¹' E) ≤ ENNReal.ofReal ε := by
    have hscaled : |s * (q w).ratio| = s * |(q w).ratio| := by
      rw [abs_mul, abs_of_pos hs]
    have hlow : a / 2 ≤ |s * (q w).ratio| := by
      rw [hscaled]
      have h := mul_lt_mul_of_pos_left (hratio w).1 hs
      dsimp [u] at h
      have he : s * (a * (1 / (2 * s))) = a / 2 := by field_simp
      rw [he] at h
      exact h.le
    have hhigh : |s * (q w).ratio| ≤ 1 := by
      rw [hscaled]
      have h := mul_le_mul_of_nonneg_left (hratio w).2 hs.le
      dsimp [u] at h
      have he : s * (1 / (2 * s)) = (1 / 2 : ℝ) := by field_simp
      rw [he] at h
      linarith
    have hb := affine_gridNeighborhood_measure_le μ (a := s * (q w).ratio)
      (b := s * (q w).shift + t) (by positivity : 0 < a / 2) hlow hhigh
      hρ1.le hδ.le hscale hsupport (fun x ↦ (hsmall x).le)
    rw [hmass] at hb
    have he : (q w) ⁻¹' E =
        (fun x : ℝ ↦ (s * (q w).ratio) * x + (s * (q w).shift + t)) ⁻¹'
          integerGridNeighborhood ρ := by
      ext x
      change (s * ((q w).ratio * x + (q w).shift) + t ∈ integerGridNeighborhood ρ) ↔
        ((s * (q w).ratio) * x + (s * (q w).shift + t) ∈ integerGridNeighborhood ρ)
      simp only [mul_add, mul_assoc, add_assoc]
    rw [he]
    exact hb
  calc
    _ ≤ ∑ w, S.wordWeight n w * ENNReal.ofReal ε :=
      Finset.sum_le_sum (fun w _ ↦ mul_le_mul' le_rfl (hbranch w))
    _ = ENNReal.ofReal ε := by rw [← Finset.sum_mul, S.wordWeight_sum, one_mul]

end ExactOverlaps.SelfSimilar.System
