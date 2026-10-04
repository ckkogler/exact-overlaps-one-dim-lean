module

public import ExactOverlaps.Probability.BlockKernelConversion
public import ExactOverlaps.Probability.PoissonContinuity

/-!
# Nonnegative integral conversion for ordered blocks

This converts the real kernel identity to the extended nonnegative integral
used by variance energy, after proving finiteness of each origin volume.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical

namespace ExactOverlaps.Poisson

lemma blockWeight_nonneg {n : ℕ} (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i)
    {t : ℝ} (ht : 0 ≤ t) (a b : Fin (n + 1)) : 0 ≤ blockWeight d t a b := by
  unfold blockWeight
  apply Finset.sum_nonneg
  intro c _
  split_ifs
  · exact cutWeight_nonneg d hd ht c
  · exact le_rfl

lemma continuous_blockWeight {n : ℕ} (d : Fin n → ℝ) (a b : Fin (n + 1)) :
    Continuous (fun t ↦ blockWeight d t a b) := by
  unfold blockWeight
  apply continuous_finsetSum
  intro c _
  by_cases h : blockPattern c a b
  · simp only [h, ite_true]
    exact continuous_cutWeight d c
  · simp only [h, ite_false]
    exact continuous_const

lemma volume_windowOrigins_ne_top {n : ℕ} (x : Fin (n + 1) → ℝ) (hx : Monotone x)
    (r : ℝ) (a b : Fin (n + 1)) (hab : a ≤ b) :
    volume (windowOrigins x r a b) ≠ ∞ := by
  have hs : windowOrigins x r a b ⊆ Ioc (x b - r) (x a) := by
    intro s hs
    have h := (windowIndices_eq_Icc_iff x hx s r a b hab).mp hs
    exact ⟨by linarith [h.2.1], h.1⟩
  apply (lt_of_le_of_lt (measure_mono hs) ?_).ne
  rw [Real.volume_Ioc]
  exact ENNReal.ofReal_lt_top

lemma lintegral_block_kernel_conversion {n : ℕ} (x : ℕ → ℝ)
    (hx : StrictMono (fun z : Fin (n + 1) ↦ x z.val))
    (a b : Fin (n + 1)) (hab : a < b) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t * blockWeight (orderedGapLength x n) t a b)) =
      6 * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (1 / r ^ 4) *
        volume (windowOrigins (fun z : Fin (n + 1) ↦ x z.val) r a b) := by
  have hd (i : Fin n) : 0 ≤ orderedGapLength x n i := by
    exact sub_nonneg.mpr (hx.monotone (show i.castSucc ≤ i.succ by
      change i.val ≤ i.val + 1; omega))
  have hconv := block_kernel_conversion x hx a b hab
  have hn : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0),
      0 ≤ t * blockWeight (orderedGapLength x n) t a b := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg ht.le (blockWeight_nonneg _ hd ht.le a b)
  have hm : ∀ᵐ r : ℝ ∂volume.restrict (Ioi 0),
      0 ≤ (volume (windowOrigins (fun z : Fin (n + 1) ↦ x z.val) r a b)).toReal / r ^ 4 :=
    Filter.Eventually.of_forall (fun _ ↦ by positivity)
  rw [← ofReal_integral_eq_lintegral_ofReal hconv.1 hn, hconv.2.2,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6),
    ofReal_integral_eq_lintegral_ofReal hconv.2.1 hm]
  norm_num only [ENNReal.ofReal_ofNat]
  congr 1
  apply lintegral_congr
  intro r
  rw [div_eq_mul_inv, mul_comm, ← one_div,
    ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / r ^ 4),
    ENNReal.ofReal_toReal (volume_windowOrigins_ne_top _ hx.monotone r a b hab.le)]

end ExactOverlaps.Poisson
