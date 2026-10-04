module

public import ExactOverlaps.SelfSimilar.QuantizedCoupling
public import ExactOverlaps.SelfSimilar.DisplacementEntropy

/-!
Dyadic entropy comparison under a coupling with rare large displacements.
The estimate records the exceptional probability, so a support interval
whose logarithmic size grows linearly remains usable in asymptotic arguments.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal Classical

namespace ExactOverlaps.Entropy

variable {Ω : Type*} [MeasurableSpace Ω]

theorem integerCouplingLaw_map_bool_apply (P : ProbabilityMeasure Ω) (f g : Ω → ℤ)
    (hf : Measurable f) (hg : Measurable g) (F : ℤ × ℤ → Bool) (b : Bool) :
    ((integerCouplingLaw P f g).map F) b =
      (P : Measure Ω) {x | F (f x, g x) = b} := by
  have hF : Measurable F := measurable_of_countable _
  rw [← PMF.toMeasure_apply_singleton _ b (measurableSet_singleton b),
    ← PMF.toMeasure_map _ _ hF]
  simp only [integerCouplingLaw, Measure.toPMF_toMeasure, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map hF (hf.prodMk hg),
    Measure.map_apply (hF.comp (hf.prodMk hg)) (measurableSet_singleton b)]
  rfl

theorem floor_sub_mem_symmetric_Icc {x y : ℝ} {K : ℕ} (h : |y - x| ≤ K) :
    ⌊y⌋ - ⌊x⌋ ∈ Icc (-((K + 1 : ℕ) : ℤ)) ((K + 1 : ℕ) : ℤ) := by
  obtain ⟨hl, hu⟩ := floor_sub_mem_Icc_of_abs_sub_le h
  constructor <;> omega

/-- Quantized coupling bound with a separate exceptional-displacement probability. -/
theorem abs_dyadicEntropy_sub_le_of_rare_coupling (P : ProbabilityMeasure Ω)
    (X Y : Ω → ℝ) (hXm : Measurable X) (hYm : Measurable Y)
    (hX : HasBoundedSupport (P.map X)) (hY : HasBoundedSupport (P.map Y))
    (i : ℤ) (K N : ℕ) {δ : ℝ}
    (hglobal : ∀ᵐ x ∂(P : Measure Ω), |(2 : ℝ) ^ i * (Y x - X x)| ≤ N)
    (hrare : ((P : Measure Ω) {x | (K : ℝ) < |(2 : ℝ) ^ i * (Y x - X x)|}).toReal ≤ δ) :
    |dyadicEntropy (P.map Y) hY i - dyadicEntropy (P.map X) hX i| ≤
      Real.log 2 + Real.log (2 * K + 3 : ℝ) + δ * Real.log (2 * N + 3 : ℝ) := by
  let f := dyadicQuantize i ∘ X
  let g := dyadicQuantize i ∘ Y
  have hf : Measurable f := (measurable_dyadicQuantize i).comp hXm
  have hg : Measurable g := (measurable_dyadicQuantize i).comp hYm
  let p := integerCouplingLaw P f g
  have hp : p.support.Finite := dyadicCoupling_support_finite P X Y hXm hYm hX hY i
  let d := p.map (fun z ↦ z.2 - z.1)
  have hd : d.support.Finite := by simpa [d] using hp.image (fun z ↦ z.2 - z.1)
  have hband : ∀ z ∈ p.support,
      z.2 - z.1 ∈ Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ) := by
    apply integerCouplingLaw_support_subset P f g hf hg
    filter_upwards [hglobal] with x hx
    apply floor_sub_mem_symmetric_Icc
    simpa only [mul_sub] using hx
  have hdglobal : ∀ z ∈ d.support,
      z ∈ Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ) := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    exact hband w hw
  have hdrare : ((d.map (fun z ↦ decide (z ∉ Icc (-((K + 1 : ℕ) : ℤ))
      ((K + 1 : ℕ) : ℤ)))) true).toReal ≤ δ := by
    rw [show d = p.map (fun z ↦ z.2 - z.1) from rfl, PMF.map_comp]
    rw [integerCouplingLaw_map_bool_apply P f g hf hg]
    apply le_trans _ hrare
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono
    intro x hx
    have hout : g x - f x ∉ Icc (-((K + 1 : ℕ) : ℤ)) ((K + 1 : ℕ) : ℤ) := by
      simpa only [Function.comp_apply, decide_eq_true_eq, Set.mem_ofPred_eq] using hx
    by_contra hnot
    change ¬ (K : ℝ) < |(2 : ℝ) ^ i * (Y x - X x)| at hnot
    apply hout
    apply floor_sub_mem_symmetric_Icc
    have hb : |(2 : ℝ) ^ i * (Y x - X x)| ≤ K := le_of_not_gt hnot
    simpa only [mul_sub] using hb
  have hdent := finiteEntropy_le_of_rare_large_integer d hd (K + 1) (N + 1) hdglobal hdrare
  have hcomp := (abs_snd_entropy_sub_fst_le_displacement_entropy p hp).trans hdent
  have hfst : p.map Prod.fst = dyadicLaw (P.map X) i :=
    (integerCouplingLaw_map_fst P f g hf hg).trans (dyadicLaw_map P X hXm i).symm
  have hsnd : p.map Prod.snd = dyadicLaw (P.map Y) i :=
    (integerCouplingLaw_map_snd P f g hf hg).trans (dyadicLaw_map P Y hYm i).symm
  have hK : 2 * ((K + 1 : ℕ) : ℝ) + 1 = 2 * K + 3 := by push_cast; ring
  have hN : 2 * ((N + 1 : ℕ) : ℝ) + 1 = 2 * N + 3 := by push_cast; ring
  simpa only [hfst, hsnd, hK, hN, dyadicEntropy] using hcomp

end ExactOverlaps.Entropy
