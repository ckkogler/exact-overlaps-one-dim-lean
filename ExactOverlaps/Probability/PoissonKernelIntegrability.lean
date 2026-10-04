module

public import ExactOverlaps.Probability.PoissonBoundaryKernels

/-!
# Integrability of interior and boundary cell kernels

Positive block diameter makes both the time-weighted survival kernels and
the scale-weighted origin lengths integrable. These certificates justify
conversion of their exact real integral identities to nonnegative integrals.
-/

@[expose] public section

open MeasureTheory Set

namespace ExactOverlaps.Poisson

lemma integrableOn_time_cellSurvival {d l u : ℝ}
    (hd : 0 < d) (hl : 0 ≤ l) (hu : 0 ≤ u) :
    IntegrableOn (fun t : ℝ ↦ t * cellSurvival d l u t) (Ioi 0) := by
  have hi (a : ℝ) (ha : 0 < a) :
      IntegrableOn (fun t : ℝ ↦ t * Real.exp (-(a * t))) (Ioi 0) := by
    simpa using integrableOn_pow_mul_exp ha 1
  have hdl := add_pos_of_pos_of_nonneg hd hl
  have hdu := add_pos_of_pos_of_nonneg hd hu
  have hdlu := add_pos_of_pos_of_nonneg hdl hu
  have h := (((hi d hd).sub (hi (d + l) hdl)).sub (hi (d + u) hdu)).add
    (hi (d + l + u) hdlu)
  exact h.congr_fun (fun _ _ ↦ by simp [cellSurvival_expand, mul_add, mul_sub])
    measurableSet_Ioi

lemma integrableOn_cellOffsetLength {d l u : ℝ}
    (hd : 0 < d) (hl : 0 ≤ l) (hu : 0 ≤ u) :
    IntegrableOn (fun r : ℝ ↦ cellOffsetLength d l u r / r ^ 4) (Ioi 0) := by
  have hdl := add_pos_of_pos_of_nonneg hd hl
  have hdu := add_pos_of_pos_of_nonneg hd hu
  have hdlu := add_pos_of_pos_of_nonneg hdl hu
  have h := (((integrableOn_positive_offset_length hd).sub
    (integrableOn_positive_offset_length hdl)).sub
    (integrableOn_positive_offset_length hdu)).add
    (integrableOn_positive_offset_length hdlu)
  exact h.congr_fun (fun _ _ ↦ by simp [cellOffsetLength, add_div, sub_div])
    measurableSet_Ioi

lemma integrableOn_time_boundarySurvival {d l : ℝ} (hd : 0 < d) (hl : 0 ≤ l) :
    IntegrableOn (fun t : ℝ ↦ t * boundarySurvival d l t) (Ioi 0) := by
  have hi (a : ℝ) (ha : 0 < a) :
      IntegrableOn (fun t : ℝ ↦ t * Real.exp (-(a * t))) (Ioi 0) := by
    simpa using integrableOn_pow_mul_exp ha 1
  have h := (hi d hd).sub (hi (d + l) (add_pos_of_pos_of_nonneg hd hl))
  exact h.congr_fun (fun _ _ ↦ by simp [boundarySurvival_expand, mul_sub])
    measurableSet_Ioi

lemma integrableOn_boundaryOffsetLength {d l : ℝ} (hd : 0 < d) (hl : 0 ≤ l) :
    IntegrableOn (fun r : ℝ ↦ boundaryOffsetLength d l r / r ^ 4) (Ioi 0) := by
  have h := (integrableOn_positive_offset_length hd).sub
    (integrableOn_positive_offset_length (add_pos_of_pos_of_nonneg hd hl))
  exact h.congr_fun (fun _ _ ↦ by simp [boundaryOffsetLength, sub_div])
    measurableSet_Ioi

end ExactOverlaps.Poisson
