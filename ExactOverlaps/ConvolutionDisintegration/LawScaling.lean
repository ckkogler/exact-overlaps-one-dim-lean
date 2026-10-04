/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.ConvolutionDisintegration.Admissibility

/-!
# Signed dilation of actual probability laws

Pushforward by multiplication is measurable on the law space. It commutes
with convolution, multiplies variance by the square of the scalar and
multiplies support interval width by its absolute value.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace ExactOverlaps.ConvolutionDisintegration

def scaleLaw (a : ℝ) (μ : ProbabilityMeasure ℝ) : ProbabilityMeasure ℝ :=
  μ.map (fun x ↦ a * x)

lemma measurable_scaleLaw (a : ℝ) : Measurable (scaleLaw a) :=
  ((Measure.measurable_map (fun x : ℝ ↦ a * x) (by fun_prop)).comp
    measurable_subtype_coe).subtype_mk

lemma variance_scaleLaw (a : ℝ) (μ : ProbabilityMeasure ℝ) :
    variance (id : ℝ → ℝ) (scaleLaw a μ : Measure ℝ) =
      a ^ 2 * variance (id : ℝ → ℝ) (μ : Measure ℝ) := by
  rw [scaleLaw, ProbabilityMeasure.toMeasure_map,
    variance_map measurable_id.aemeasurable (by fun_prop)]
  exact variance_const_mul a (id : ℝ → ℝ) (μ : Measure ℝ)

lemma scaleLaw_convolution (a : ℝ) (μ ν : ProbabilityMeasure ℝ) :
    Entropy.realConvolution (scaleLaw a μ) (scaleLaw a ν) =
      scaleLaw a (Entropy.realConvolution μ ν) := by
  apply ProbabilityMeasure.toMeasure_injective
  change (((μ : Measure ℝ).map (fun x ↦ a * x)).prod
      ((ν : Measure ℝ).map (fun x ↦ a * x))).map (fun z : ℝ × ℝ ↦ z.1 + z.2) =
    (((μ : Measure ℝ).prod (ν : Measure ℝ)).map (fun z : ℝ × ℝ ↦ z.1 + z.2)).map
      (fun x ↦ a * x)
  have hm : Measurable (fun x : ℝ ↦ a * x) := by fun_prop
  have hs : Measurable (fun z : ℝ × ℝ ↦ z.1 + z.2) := measurable_fst.add measurable_snd
  rw [Measure.map_prod_map _ _ hm hm, Measure.map_map hs (hm.prodMap hm),
    Measure.map_map hm hs]
  congr 1
  funext z
  exact (mul_add a z.1 z.2).symm

lemma scaleLaw_zero (a : ℝ) : scaleLaw a Entropy.zeroRealLaw = Entropy.zeroRealLaw := by
  apply ProbabilityMeasure.toMeasure_injective
  change (Measure.dirac (0 : ℝ)).map (fun x ↦ a * x) = Measure.dirac 0
  rw [Measure.map_dirac' (by fun_prop), mul_zero]

lemma scaleLaw_inverse {a : ℝ} (ha : a ≠ 0) (μ : ProbabilityMeasure ℝ) :
    scaleLaw a⁻¹ (scaleLaw a μ) = μ := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((μ : Measure ℝ).map (fun x ↦ a * x)).map (fun x ↦ a⁻¹ * x) = _
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have he : (fun x : ℝ ↦ a⁻¹ * x) ∘ (fun x ↦ a * x) = id := by
    funext x
    simp [ha]
  rw [he, Measure.map_id]

lemma HasIntervalWidth.scaleLaw {μ : ProbabilityMeasure ℝ} {r : ℝ}
    (h : HasIntervalWidth μ r) (a : ℝ) : HasIntervalWidth (scaleLaw a μ) (|a| * r) := by
  obtain ⟨b, hb⟩ := h
  by_cases ha : 0 ≤ a
  · refine ⟨a * b, ?_⟩
    change ∀ᵐ x ∂((μ : Measure ℝ).map (fun x ↦ a * x)), x ∈ Icc (a * b) (a * b + |a| * r)
    apply (ae_map_iff (by fun_prop) measurableSet_Icc).mpr
    filter_upwards [hb] with x hx
    rw [abs_of_nonneg ha]
    constructor <;> nlinarith [hx.1, hx.2]
  · have ha' : a ≤ 0 := (lt_of_not_ge ha).le
    refine ⟨a * (b + r), ?_⟩
    change ∀ᵐ x ∂((μ : Measure ℝ).map (fun x ↦ a * x)),
      x ∈ Icc (a * (b + r)) (a * (b + r) + |a| * r)
    apply (ae_map_iff (by fun_prop) measurableSet_Icc).mpr
    filter_upwards [hb] with x hx
    rw [abs_of_nonpos ha']
    constructor <;> nlinarith [hx.1, hx.2]

end ExactOverlaps.ConvolutionDisintegration
