module

public import ExactOverlaps.Probability.CutBlockBoundaryProbability
public import ExactOverlaps.Probability.WindowBlockGeometry
public import ExactOverlaps.Probability.PoissonKernelIntegrability

/-!
# Exact conversion for each nontrivial ordered block

For every block of positive diameter, the time-weighted cut probability has
six times the integral of its scale-weighted window-origin volume. Both
integrals carry explicit integrability certificates.
-/

@[expose] public section

open MeasureTheory Set

namespace ExactOverlaps.Poisson

lemma block_kernel_conversion {n : ℕ} (x : ℕ → ℝ)
    (hx : StrictMono (fun z : Fin (n + 1) ↦ x z.val))
    (a b : Fin (n + 1)) (hab : a < b) :
    IntegrableOn (fun t : ℝ ↦ t * blockWeight (orderedGapLength x n) t a b) (Ioi 0) ∧
    IntegrableOn (fun r : ℝ ↦
      (volume (windowOrigins (fun z : Fin (n + 1) ↦ x z.val) r a b)).toReal / r ^ 4)
        (Ioi 0) ∧
    (∫ t : ℝ in Ioi 0, t * blockWeight (orderedGapLength x n) t a b) =
      6 * ∫ r : ℝ in Ioi 0,
        (volume (windowOrigins (fun z : Fin (n + 1) ↦ x z.val) r a b)).toReal / r ^ 4 := by
  have hgap (i : Fin n) : 0 ≤ x (i.val + 1) - x i.val := by
    exact sub_nonneg.mpr (hx.monotone (show i.castSucc ≤ i.succ by
      change i.val ≤ i.val + 1; omega))
  revert hab
  refine Fin.cases ?_ (fun i ↦ ?_) a
  · refine Fin.lastCases ?_ (fun j ↦ ?_) b
    · intro hab
      have hd : 0 < x n - x 0 := sub_pos.mpr (hx hab)
      simp_rw [ordered_blockWeight_full, volume_windowOrigins_full _ hx.monotone,
        ENNReal.toReal_ofReal (le_max_right _ _)]
      refine ⟨?_, integrableOn_positive_offset_length hd,
        integral_time_survival_eq_six_offset hd⟩
      simpa using integrableOn_pow_mul_exp hd 1
    · intro hab
      have hd : 0 < x j.val - x 0 := sub_pos.mpr (hx hab)
      simp_rw [ordered_blockWeight_left, volume_windowOrigins_left _ hx.monotone]
      simp only [Fin.val_zero, Fin.val_castSucc, Fin.val_succ]
      simp_rw [ENNReal.toReal_ofReal (boundaryOffsetLength_nonneg (d := x j.val - x 0) (hgap j))]
      exact ⟨integrableOn_time_boundarySurvival hd (hgap j),
        integrableOn_boundaryOffsetLength hd (hgap j),
        integral_time_boundarySurvival_eq_six_offset hd (hgap j)⟩
  · refine Fin.lastCases ?_ (fun j ↦ ?_) b
    · intro hab
      have hd : 0 < x n - x (i.val + 1) := sub_pos.mpr (hx hab)
      simp_rw [ordered_blockWeight_right, volume_windowOrigins_right _ hx.monotone]
      simp only [Fin.val_last, Fin.val_castSucc, Fin.val_succ]
      simp_rw [ENNReal.toReal_ofReal (boundaryOffsetLength_nonneg
        (d := x n - x (i.val + 1)) (hgap i))]
      exact ⟨integrableOn_time_boundarySurvival hd (hgap i),
        integrableOn_boundaryOffsetLength hd (hgap i),
        integral_time_boundarySurvival_eq_six_offset hd (hgap i)⟩
    · intro hab
      have hd : 0 < x j.val - x (i.val + 1) := sub_pos.mpr (hx hab)
      simp_rw [ordered_blockWeight_interior x _ i j hab.le,
        volume_windowOrigins_interior _ hx.monotone _ i j hab.le]
      simp only [Fin.val_castSucc, Fin.val_succ]
      simp_rw [ENNReal.toReal_ofReal (cellOffsetLength_nonneg
        (d := x j.val - x (i.val + 1)) (hgap i) (hgap j))]
      exact ⟨integrableOn_time_cellSurvival hd (hgap i) (hgap j),
        integrableOn_cellOffsetLength hd (hgap i) (hgap j),
        integral_time_cellSurvival_eq_six_offset hd (hgap i) (hgap j)⟩

end ExactOverlaps.Poisson
