module

public import ExactOverlaps.SelfSimilar.RatioTailBounds
public import ExactOverlaps.SelfSimilar.RatioTailScaleBounds

/-!
At a fixed super-Lyapunov scale, every typical ratio tail has uniformly the
expected entropy per letter. The class-window width is chosen after accuracy.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ExactOverlaps.SelfSimilar.System

open Entropy
variable {ι : Type*} [Fintype ι]

theorem ratioScaledEntropy_target_uniform_on_typical (S : System ι)
    (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ) {d q : ℝ}
    (hlim : Tendsto (normalizedDyadicEntropy μ hμ) atTop (𝓝 d))
    (hd : 0 ≤ d) (hq : 1 < q) {τ : ℝ} (hτ : 0 < τ) :
    ∃ η > 0, ∀ᶠ n : ℕ in atTop, ∀ r : (S.wordRatioLaw n).support,
      (S.dyadicLyapunov - η) * n ≤ (ratioLevel r : ℝ) →
      (ratioLevel r : ℝ) ≤ (S.dyadicLyapunov + η) * n →
      |dyadicEntropy (S.ratioScaledProbability μ n r)
          (S.ratioScaledProbability_hasBoundedSupport μ hμ n r)
          (targetRatioLevel S.dyadicLyapunov q n) / n -
        d * ((q - 1) * S.dyadicLyapunov) * Real.log 2| ≤ τ := by
  let c := (q - 1) * S.dyadicLyapunov
  have hc : 0 < c := mul_pos (sub_pos.mpr hq) S.dyadicLyapunov_pos
  let L := Real.log 2
  have hL : 0 < L := Real.log_pos (by norm_num)
  let A := c + 1
  have hA : 0 < A := by dsimp [A]; linarith
  let η := min (c / 2) (min 1 (τ / (8 * (d + 1) * L)))
  have hη : 0 < η := lt_min (by positivity) (lt_min zero_lt_one (by positivity))
  have hηc : η ≤ c / 2 := min_le_left _ _
  have hηone : η ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hητ : η * (8 * (d + 1) * L) ≤ τ :=
    (le_div_iff₀ (by positivity)).mp ((min_le_right _ _).trans (min_le_right _ _))
  let δ := τ / (4 * A * L)
  have hδ : 0 < δ := by positivity
  obtain ⟨M, hM⟩ := uniform_affine_fine_entropy_limit μ hμ hlim
    (show (0 : ℝ) < 1 / 2 by norm_num) 1 hδ
  have hbuffer := eventually_typical_level_buffers (κ := S.dyadicLyapunov) (q := q) hη
    (show 0 < (q - 1) * S.dyadicLyapunov - η by change 0 < c - η; linarith) (M + 1)
  have hinv : ∀ᶠ n : ℕ in atTop, (1 : ℝ) / n < η :=
    (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).eventually (gt_mem_nhds hη)
  refine ⟨η, hη, ?_⟩
  filter_upwards [hbuffer, hinv, eventually_gt_atTop 0] with n hbuf hninv hn
  intro r hrlo hrhi
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let j := ratioLevel (r : ℝ)
  let f := targetRatioLevel S.dyadicLyapunov q n
  let m := (f - j).toNat
  have hgap : ((M + 1 : ℕ) : ℤ) ≤ f - j := (hbuf j hrlo hrhi).2
  have hmn : M ≤ m := by dsimp [m]; omega
  have hmpos : 0 < m := by dsimp [m]; omega
  have hmcast : (m : ℤ) = f - j := Int.toNat_of_nonneg (by omega)
  have hmreal : (m : ℝ) = ((f - j : ℤ) : ℝ) := by exact_mod_cast hmcast
  have hjm : j + (m : ℤ) = f := by omega
  have herr := hM m hmn hmpos j (S.ratioDilation n r)
    (by simpa only [ratioDilation] using
      (half_lt_ratioLevel_mul (S.wordRatioLaw_support_ne_zero n r)).le)
    (by simpa only [ratioDilation, Nat.cast_one] using
      ratioLevel_mul_le_one (S.wordRatioLaw_support_ne_zero n r))
  rw [hjm] at herr
  have hsc := typical_remainder_ratio_bounds hn hrlo hrhi (q := q)
  have hnear : |(m : ℝ) / n - c| ≤ 2 * η := by
    rw [hmreal]
    exact hsc.1.trans (by linarith)
  have hupper : (m : ℝ) / n ≤ A := by
    rw [hmreal]
    exact hsc.2.trans (by dsimp [A, c]; linarith)
  have hb := normalized_tail_error_bound hn' hd hδ.le hL.le herr.le hnear hupper
  have hδeq : δ * A * L = τ / 4 := by dsimp [δ]; field_simp
  have hηL : 0 ≤ η * L := mul_nonneg hη.le hL.le
  have hsmall : 2 * d * η * L ≤ τ / 4 := by nlinarith
  change |dyadicEntropy (S.ratioScaledProbability μ n r) _ f / n - d * c * L| ≤ τ
  change |dyadicEntropy (S.ratioScaledProbability μ n r)
    (S.ratioScaledProbability_hasBoundedSupport μ hμ n r) f / n - d * c * L| ≤
    δ * A * L + 2 * d * η * L at hb
  rw [hδeq] at hb
  linarith

end ExactOverlaps.SelfSimilar.System
