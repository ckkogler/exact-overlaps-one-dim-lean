module

public import ExactOverlaps.Probability.WindowBlockIntegration
public import ExactOverlaps.Probability.BlockKernelNonnegative

/-!
# The two nontrivial block kernels

Singleton blocks have zero variance coefficient. The remaining blocks carry
measurable time and scale kernels with an exact factor-six integral relation.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical

namespace ExactOverlaps.Poisson

noncomputable def blockTimeKernel {n : ℕ} (x : ℕ → ℝ) (a b : Fin (n + 1))
    (t : ℝ) : ℝ := if a < b then t * blockWeight (orderedGapLength x n) t a b else 0

noncomputable def blockEnergyKernel {n : ℕ} (x : Fin (n + 1) → ℝ)
    (a b : Fin (n + 1)) (r : ℝ) : ℝ≥0∞ :=
  if a < b then ENNReal.ofReal (1 / r ^ 4) * volume (windowOrigins x r a b) else 0

lemma continuous_volume_windowOrigins {n : ℕ} (x : Fin (n + 1) → ℝ)
    (hx : Monotone x) (a b : Fin (n + 1)) (hab : a ≤ b) :
    Continuous (fun r ↦ volume (windowOrigins x r a b)) := by
  revert hab
  refine Fin.cases ?_ (fun i ↦ ?_) a
  · refine Fin.lastCases ?_ (fun j ↦ ?_) b
    · intro _
      simp_rw [volume_windowOrigins_full x hx]
      apply ENNReal.continuous_ofReal.comp
      fun_prop
    · intro _
      simp_rw [volume_windowOrigins_left x hx]
      unfold boundaryOffsetLength
      apply ENNReal.continuous_ofReal.comp
      fun_prop
  · refine Fin.lastCases ?_ (fun j ↦ ?_) b
    · intro _
      simp_rw [volume_windowOrigins_right x hx]
      unfold boundaryOffsetLength
      apply ENNReal.continuous_ofReal.comp
      fun_prop
    · intro hab
      simp_rw [volume_windowOrigins_interior x hx _ i j hab]
      unfold cellOffsetLength
      apply ENNReal.continuous_ofReal.comp
      fun_prop

lemma measurable_blockEnergyKernel {n : ℕ} (x : Fin (n + 1) → ℝ)
    (hx : Monotone x) (a b : Fin (n + 1)) : Measurable (blockEnergyKernel x a b) := by
  unfold blockEnergyKernel
  by_cases hab : a < b
  · simp only [hab, ite_true]
    exact ((measurable_const.div (measurable_id.pow_const 4)).ennreal_ofReal).mul
      (continuous_volume_windowOrigins x hx a b hab.le).measurable
  · simp only [hab, ite_false]
    exact measurable_const

lemma continuous_blockTimeKernel {n : ℕ} (x : ℕ → ℝ) (a b : Fin (n + 1)) :
    Continuous (blockTimeKernel x a b) := by
  unfold blockTimeKernel
  by_cases hab : a < b
  · simp only [hab, ite_true]
    exact continuous_id.mul (continuous_blockWeight _ a b)
  · simp only [hab, ite_false]
    exact continuous_const

lemma blockTimeKernel_nonneg {n : ℕ} (x : ℕ → ℝ)
    (hx : Monotone (fun z : Fin (n + 1) ↦ x z.val)) (a b : Fin (n + 1))
    {t : ℝ} (ht : 0 ≤ t) : 0 ≤ blockTimeKernel x a b t := by
  unfold blockTimeKernel
  split_ifs
  · apply mul_nonneg ht (blockWeight_nonneg _ ?_ ht a b)
    intro i
    exact sub_nonneg.mpr (hx (show i.castSucc ≤ i.succ by
      change i.val ≤ i.val + 1; omega))
  · exact le_rfl

lemma lintegral_blockTimeKernel {n : ℕ} (x : ℕ → ℝ)
    (hx : StrictMono (fun z : Fin (n + 1) ↦ x z.val)) (a b : Fin (n + 1)) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (blockTimeKernel x a b t)) =
      6 * ∫⁻ r in Ioi (0 : ℝ), blockEnergyKernel (fun z ↦ x z.val) a b r := by
  by_cases hab : a < b
  · simp only [blockTimeKernel, blockEnergyKernel, hab, ite_true]
    exact lintegral_block_kernel_conversion x hx a b hab
  · simp [blockTimeKernel, blockEnergyKernel, hab]

end ExactOverlaps.Poisson
