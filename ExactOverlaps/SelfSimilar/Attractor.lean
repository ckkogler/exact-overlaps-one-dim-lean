module

public import ExactOverlaps.SelfSimilar.StationaryUniqueness
public import ExactOverlaps.SelfSimilar.Dimension
public import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
The actual coding attractor is a compact nonempty set, is invariant under
the given similarities, and carries every stationary probability law.
Its definition uses all branches, including branches of weight zero.
-/

@[expose] public section

open MeasureTheory Set
open scoped Topology ENNReal

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι]

/-- The image of all infinite addresses under the convergent affine coding. -/
noncomputable def attractor (S : System ι) : Set ℝ := range S.coding

theorem continuous_codingTerm [TopologicalSpace ι] [DiscreteTopology ι]
    (S : System ι) (n : ℕ) : Continuous (S.codingTerm n) := by
  have hr : Continuous (fun i ↦ (S.map i).ratio) := continuous_of_discreteTopology
  have hb : Continuous (fun i ↦ (S.map i).shift) := continuous_of_discreteTopology
  unfold codingTerm prefixRatio
  exact (continuous_finsetProd _ (fun j _ ↦ hr.comp (continuous_apply j))).mul
    (hb.comp (continuous_apply n))

theorem continuous_coding [TopologicalSpace ι] [DiscreteTopology ι]
    (S : System ι) : Continuous S.coding := by
  obtain ⟨c, M, hc, hc1, _, hmax, hshift⟩ := S.exists_uniform_bounds
  exact continuous_tsum (S.continuous_codingTerm)
    ((summable_geometric_of_lt_one hc.le hc1).mul_right M)
    (fun n ω ↦ by simpa only [Real.norm_eq_abs] using
      S.abs_codingTerm_le hc.le hmax hshift n ω)

theorem attractor_isCompact (S : System ι) : IsCompact S.attractor := by
  let : TopologicalSpace ι := ⊥
  let : DiscreteTopology ι := ⟨rfl⟩
  exact isCompact_range S.continuous_coding

theorem attractor_nonempty (S : System ι) : S.attractor.Nonempty := by
  let := S.nonempty_index
  exact range_nonempty _

theorem attractor_eq_union (S : System ι) :
    S.attractor = ⋃ i, (S.map i) '' S.attractor := by
  ext x
  constructor
  · rintro ⟨ω, rfl⟩
    exact mem_iUnion.mpr ⟨ω 0, ⟨S.coding (Bernoulli.shift ω),
      ⟨Bernoulli.shift ω, rfl⟩, (S.coding_shift ω).symm⟩⟩
  · intro hx
    obtain ⟨i, y, ⟨ω, rfl⟩, rfl⟩ := mem_iUnion.mp hx
    let η : ℕ → ι := fun n ↦ Nat.casesOn n i ω
    refine ⟨η, ?_⟩
    have he : Bernoulli.shift η = ω := rfl
    rw [S.coding_shift η, he]
    rfl

theorem map_attractor_subset (S : System ι) (i : ι) :
    (S.map i) '' S.attractor ⊆ S.attractor := by
  intro x hx
  rw [S.attractor_eq_union]
  exact mem_iUnion.mpr ⟨i, hx⟩

theorem codingMeasure_attractor [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (S : System ι) : S.codingMeasure S.attractor = 1 := by
  rw [codingMeasure, Measure.map_apply S.measurable_coding S.attractor_isCompact.measurableSet]
  have he : S.coding ⁻¹' S.attractor = univ := by
    ext ω
    simp only [mem_preimage, mem_univ, iff_true]
    exact ⟨ω, rfl⟩
  rw [he, measure_univ]

theorem stationary_attractor (S : System ι) (μ : ProbabilityMeasure ℝ)
    (hμ : S.IsStationary (μ : Measure ℝ)) : (μ : Measure ℝ) S.attractor = 1 := by
  let : MeasurableSpace ι := ⊤
  rw [S.stationary_eq_codingMeasure μ hμ]
  exact S.codingMeasure_attractor

theorem dimension_le_attractor (S : System ι) (μ : ProbabilityMeasure ℝ)
    (hμ : S.IsStationary (μ : Measure ℝ)) :
    lowerHausdorffDimension (μ : Measure ℝ) ≤ dimH S.attractor :=
  lowerHausdorffDimension_le_dimH _ S.attractor_isCompact.measurableSet
    (by rw [S.stationary_attractor μ hμ]; exact zero_lt_one)

end ExactOverlaps.SelfSimilar.System
