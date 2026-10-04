/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.ConvolutionDisintegration.LawScaling

/-!
# Common signed dilation of a variable finite factor family

All factors are pushed forward by the same real scalar. The count stays
positive, the represented sum law is dilated, and the cost agrees exactly
at the corresponding physical scale.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace ExactOverlaps.ConvolutionDisintegration

def scaleTuple (a : ℝ) : (n : ℕ) → Entropy.FiniteTuple (ProbabilityMeasure ℝ) n →
    Entropy.FiniteTuple (ProbabilityMeasure ℝ) n
  | 0, w => w
  | n + 1, w => (scaleLaw a w.1, scaleTuple a n w.2)

def scaleFamily (a : ℝ) (c : FactorFamily) : FactorFamily :=
  ⟨c.1, scaleTuple a (c.1 + 1) c.2⟩

lemma measurable_scaleTuple (a : ℝ) : ∀ n, Measurable (scaleTuple a n) := by
  intro n
  induction n with
  | zero => exact measurable_id
  | succ n ih =>
    exact ((measurable_scaleLaw a).comp measurable_fst).prodMk
      (ih.comp measurable_snd)

lemma measurable_scaleFamily (a : ℝ) : Measurable (scaleFamily a) :=
  measurable_from_sigma _ (fun n ↦
    (measurable_sigma_injection n).comp (measurable_scaleTuple a (n + 1)))

lemma factorCount_scaleFamily (a : ℝ) (c : FactorFamily) :
    factorCount (scaleFamily a c) = factorCount c := rfl

lemma tupleConvolution_scaleTuple (a : ℝ) (n : ℕ)
    (w : Entropy.FiniteTuple (ProbabilityMeasure ℝ) n) :
    Entropy.tupleConvolution id n (scaleTuple a n w) =
      scaleLaw a (Entropy.tupleConvolution id n w) := by
  induction n with
  | zero => exact (scaleLaw_zero a).symm
  | succ n ih =>
    change Entropy.realConvolution (scaleLaw a w.1)
      (Entropy.tupleConvolution id n (scaleTuple a n w.2)) =
      scaleLaw a (Entropy.realConvolution w.1 (Entropy.tupleConvolution id n w.2))
    rw [ih w.2, scaleLaw_convolution]

lemma convolutionLaw_scaleFamily (a : ℝ) (c : FactorFamily) :
    convolutionLaw (scaleFamily a c) = scaleLaw a (convolutionLaw c) :=
  tupleConvolution_scaleTuple a (c.1 + 1) c.2

lemma tupleVariance_scaleTuple (a : ℝ) (n : ℕ)
    (w : Entropy.FiniteTuple (ProbabilityMeasure ℝ) n) :
    Entropy.tupleSum (fun μ : ProbabilityMeasure ℝ ↦ variance (id : ℝ → ℝ) (μ : Measure ℝ))
      n (scaleTuple a n w) = a ^ 2 *
    Entropy.tupleSum (fun μ : ProbabilityMeasure ℝ ↦ variance (id : ℝ → ℝ) (μ : Measure ℝ)) n w := by
  induction n with
  | zero => exact (mul_zero _).symm
  | succ n ih =>
    change variance (id : ℝ → ℝ) (scaleLaw a w.1 : Measure ℝ) +
      Entropy.tupleSum _ n (scaleTuple a n w.2) =
      a ^ 2 * (variance (id : ℝ → ℝ) (w.1 : Measure ℝ) + Entropy.tupleSum _ n w.2)
    rw [variance_scaleLaw, ih w.2, mul_add]

lemma totalVariance_scaleFamily (a : ℝ) (c : FactorFamily) :
    totalVariance (scaleFamily a c) = a ^ 2 * totalVariance c :=
  tupleVariance_scaleTuple a (c.1 + 1) c.2

lemma admissible_scaleTuple (a : ℝ) {r : ℝ} (n : ℕ)
    (w : Entropy.FiniteTuple (ProbabilityMeasure ℝ) n)
    (hw : ∀ j, HasIntervalWidth (Entropy.tupleCoordinate n w j) r) :
    ∀ j, HasIntervalWidth (Entropy.tupleCoordinate n (scaleTuple a n w) j) (|a| * r) := by
  induction n with
  | zero => intro j; exact Fin.elim0 j
  | succ n ih =>
    intro j
    exact Fin.cases ((hw 0).scaleLaw a) (ih w.2 (fun k ↦ hw k.succ)) j

lemma admissible_scaleFamily (a : ℝ) {r : ℝ} {c : FactorFamily}
    (hc : Admissible r c) : Admissible (|a| * r) (scaleFamily a c) :=
  admissible_scaleTuple a (c.1 + 1) c.2 hc

lemma cost_scaleFamily {a r : ℝ} (ha : a ≠ 0) (hr : 0 < r) (c : FactorFamily) :
    cost (|a| * r) (scaleFamily a c) = cost r c := by
  unfold cost
  rw [totalVariance_scaleFamily, mul_pow, sq_abs]
  congr 1
  field_simp

end ExactOverlaps.ConvolutionDisintegration
