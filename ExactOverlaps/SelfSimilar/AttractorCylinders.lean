module

public import ExactOverlaps.SelfSimilar.Attractor
public import ExactOverlaps.SelfSimilar.SimilarityDimension

/-!
Every level of the actual affine cylinders covers the attractor. Their
diameters decay uniformly and their powers sum according to the Moran
pressure, without any separation assumption.
-/

@[expose] public section

open Set Metric MeasureTheory
open scoped ENNReal

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι]

theorem exists_word_preimage (S : System ι) (n : ℕ) (x : ℝ) (hx : x ∈ S.attractor) :
    ∃ w : Word ι n, ∃ y ∈ S.attractor, S.wordMap n w y = x := by
  induction n generalizing x with
  | zero => exact ⟨PUnit.unit, x, hx, RealSimilarity.identity_apply x⟩
  | succ n ih =>
    rw [S.attractor_eq_union] at hx
    obtain ⟨i, y, hy, rfl⟩ := mem_iUnion.mp hx
    obtain ⟨w, z, hz, he⟩ := ih y hy
    refine ⟨(i, w), z, hz, ?_⟩
    change (S.map i).comp (S.wordMap n w) z = S.map i y
    rw [RealSimilarity.comp_apply, he]

theorem attractor_subset_word_union (S : System ι) (n : ℕ) :
    S.attractor ⊆ ⋃ w : Word ι n, (S.wordMap n w) '' S.attractor := by
  intro x hx
  obtain ⟨w, y, hy, he⟩ := S.exists_word_preimage n x hx
  exact mem_iUnion.mpr ⟨w, ⟨y, hy, he⟩⟩

theorem exists_attractor_dist_bound (S : System ι) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x ∈ S.attractor, ∀ y ∈ S.attractor, dist x y ≤ D := by
  obtain ⟨c, M, hc, hc1, hM, hmax, hshift⟩ := S.exists_uniform_bounds
  refine ⟨2 * (M / (1 - c)), by positivity, ?_⟩
  rintro _ ⟨ω, rfl⟩ _ ⟨η, rfl⟩
  rw [Real.dist_eq]
  have hω := S.abs_coding_le hc.le hc1 hmax hshift ω
  have hη := S.abs_coding_le hc.le hc1 hmax hshift η
  have ht := abs_sub (S.coding ω) (S.coding η)
  linarith

theorem ediam_word_image_le (S : System ι) {D : ℝ}
    (hD : ∀ x ∈ S.attractor, ∀ y ∈ S.attractor, dist x y ≤ D)
    (n : ℕ) (w : Word ι n) :
    ediam ((S.wordMap n w) '' S.attractor) ≤ ENNReal.ofReal (|S.wordRatio n w| * D) := by
  apply ediam_le_of_forall_dist_le
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [(S.wordMap n w).dist_eq]
  exact mul_le_mul_of_nonneg_left (hD x hx y hy) (abs_nonneg _)

theorem sum_wordRatio_rpow (S : System ι) (s : ℝ) (n : ℕ) :
    (∑ w : Word ι n, |S.wordRatio n w| ^ s) = S.pressure s ^ n := by
  classical
  induction n with
  | zero =>
    change (∑ _w : PUnit, |(1 : ℝ)| ^ s) = S.pressure s ^ 0
    simp
  | succ n ih =>
    change (∑ w : ι × Word ι n, |(S.map w.1).ratio * S.wordRatio n w.2| ^ s) = _
    rw [Fintype.sum_prod_type]
    simp only [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
    simp_rw [← Finset.mul_sum, ih]
    rw [← Finset.sum_mul, pow_succ']
    rfl

theorem sum_wordRatio_ennreal_rpow (S : System ι) {s : ℝ} (hs : 0 ≤ s)
    (hpressure : S.pressure s = 1) (n : ℕ) :
    (∑ w : Word ι n, (ENNReal.ofReal |S.wordRatio n w|) ^ s) = 1 := by
  classical
  simp_rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hs]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun w _ ↦ Real.rpow_nonneg (abs_nonneg _) _),
    S.sum_wordRatio_rpow, hpressure, one_pow, ENNReal.ofReal_one]

end ExactOverlaps.SelfSimilar.System
