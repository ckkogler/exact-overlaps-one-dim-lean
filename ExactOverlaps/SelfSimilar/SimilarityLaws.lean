module

public import ExactOverlaps.SelfSimilar.Similarity
public import ExactOverlaps.Entropy.Dyadic

/-! Inverses and actual pushforward laws of signed real similarities. -/

@[expose] public section

open MeasureTheory Set

namespace ExactOverlaps.RealSimilarity

noncomputable def inverse (g : RealSimilarity) : RealSimilarity where
  ratio := g.ratio⁻¹
  ratio_ne_zero := inv_ne_zero g.ratio_ne_zero
  shift := -g.ratio⁻¹ * g.shift

@[simp] theorem inverse_apply_apply (g : RealSimilarity) (x : ℝ) :
    g.inverse (g x) = x := by
  simp only [inverse]
  field_simp [g.ratio_ne_zero]
  ring

@[simp] theorem apply_inverse_apply (g : RealSimilarity) (x : ℝ) :
    g (g.inverse x) = x := by
  simp only [inverse]
  field_simp [g.ratio_ne_zero]
  ring

theorem hasBoundedSupport_map (g : RealSimilarity) (μ : ProbabilityMeasure ℝ)
    (hμ : Entropy.HasBoundedSupport μ) : Entropy.HasBoundedSupport (μ.map g) := by
  obtain ⟨a, b, hab⟩ := hμ
  let M : ℝ := max |a| |b|
  let R : ℝ := |g.ratio| * M + |g.shift|
  refine ⟨-R, R, ?_⟩
  rw [ProbabilityMeasure.toMeasure_map]
  apply ae_map_iff g.measurable.aemeasurable measurableSet_Icc |>.mpr
  filter_upwards [hab] with x hx
  have habs : |x| ≤ M := by
    rw [abs_le]
    have ha : -|a| ≤ a := neg_abs_le a
    have hb : b ≤ |b| := le_abs_self b
    have ham := le_max_left |a| |b|
    have hbm := le_max_right |a| |b|
    constructor <;> dsimp [M] <;> linarith [hx.1, hx.2]
  have hg : |g x| ≤ R := (g.abs_apply_le x).trans
    (add_le_add (mul_le_mul_of_nonneg_left habs (abs_nonneg g.ratio)) le_rfl)
  exact abs_le.mp hg

theorem probability_map_inverse (g : RealSimilarity) (μ : ProbabilityMeasure ℝ) :
    (μ.map g).map g.inverse = μ := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map g.inverse.measurable g.measurable]
  have he : g.inverse ∘ g = id := by funext x; exact g.inverse_apply_apply x
  rw [he, Measure.map_id]

end ExactOverlaps.RealSimilarity
