module

public import ExactOverlaps.SelfSimilar.WordBounds
public import ExactOverlaps.SelfSimilar.CompactSupport
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
A finite-word coupling of the stationary measure and its translation
approximation. Each branch pairs the translation of the composition with the
image of a fresh stationary sample. This construction preserves the signed
multiplier and establishes a geometric displacement bound directly.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal Classical BigOperators

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι]

noncomputable def wordCouplingMeasure (S : System ι) (ν : ProbabilityMeasure ℝ)
    (n : ℕ) : Measure (ℝ × ℝ) :=
  ∑ w, S.wordWeight n w • (ν : Measure ℝ).map
    (fun z ↦ (S.wordTranslation n w, S.wordMap n w z))

theorem measurable_wordCoupling_branch (S : System ι) (n : ℕ) (w : Word ι n) :
    Measurable (fun z : ℝ ↦ (S.wordTranslation n w, S.wordMap n w z)) :=
  measurable_const.prodMk (S.wordMap n w).measurable

theorem wordCouplingMeasure_apply (S : System ι) (ν : ProbabilityMeasure ℝ)
    (n : ℕ) {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) :
    S.wordCouplingMeasure ν n E = ∑ w, S.wordWeight n w *
      (ν : Measure ℝ) {z | (S.wordTranslation n w, S.wordMap n w z) ∈ E} := by
  simp only [wordCouplingMeasure, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro w _
  rw [Measure.map_apply (S.measurable_wordCoupling_branch n w) hE]
  rfl

instance wordCouplingMeasure_isProbabilityMeasure (S : System ι)
    (ν : ProbabilityMeasure ℝ) (n : ℕ) : IsProbabilityMeasure (S.wordCouplingMeasure ν n) where
  measure_univ := by
    rw [S.wordCouplingMeasure_apply ν n MeasurableSet.univ]
    simpa using S.wordWeight_sum n

/-- Actual probability coupling for a finite word and an independent stationary tail. -/
noncomputable def wordCoupling (S : System ι) (ν : ProbabilityMeasure ℝ)
    (n : ℕ) : ProbabilityMeasure (ℝ × ℝ) :=
  (S.wordCouplingMeasure ν n).toProbabilityMeasure

theorem wordCoupling_map_snd (S : System ι) (ν : ProbabilityMeasure ℝ)
    (hν : S.IsStationary (ν : Measure ℝ)) (n : ℕ) :
    (S.wordCoupling ν n).map Prod.snd = ν := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext
  intro E hE
  rw [ProbabilityMeasure.toMeasure_map, Measure.map_apply measurable_snd hE]
  change S.wordCouplingMeasure ν n (Prod.snd ⁻¹' E) = (ν : Measure ℝ) E
  rw [S.wordCouplingMeasure_apply ν n (hE.preimage measurable_snd)]
  exact (S.word_decomposition hν n hE).symm

theorem wordCoupling_map_fst (S : System ι) (ν : ProbabilityMeasure ℝ) (n : ℕ) :
    ((S.wordCoupling ν n).map Prod.fst : Measure ℝ) = (S.wordTranslationLaw n).toMeasure := by
  let : MeasurableSpace (Word ι n) := ⊤
  have : MeasurableSingletonClass (Word ι n) := ⟨fun _ ↦ trivial⟩
  have hm : Measurable (S.wordTranslation n) := measurable_of_countable _
  apply Measure.ext
  intro E hE
  rw [ProbabilityMeasure.toMeasure_map, Measure.map_apply measurable_fst hE]
  change S.wordCouplingMeasure ν n (Prod.fst ⁻¹' E) = _
  rw [S.wordCouplingMeasure_apply ν n (hE.preimage measurable_fst)]
  rw [wordTranslationLaw, ← PMF.toMeasure_map _ _ hm,
    Measure.map_apply hm hE, PMF.toMeasure_apply_fintype]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hw : S.wordTranslation n w ∈ E
  · simp [hw, Set.indicator, wordLaw_apply]
  · simp [hw, Set.indicator]

/-- Geometric displacement bound for the finite-word stationary coupling. -/
theorem wordCoupling_displacement (S : System ι) (ν : ProbabilityMeasure ℝ)
    {c R : ℝ} (hc : 0 ≤ c) (hmax : ∀ i, |(S.map i).ratio| ≤ c)
    (hR : ∀ᵐ z ∂(ν : Measure ℝ), |z| ≤ R) (n : ℕ) :
    ∀ᵐ z ∂(S.wordCoupling ν n : Measure (ℝ × ℝ)), |z.2 - z.1| ≤ c ^ n * R := by
  rw [ae_iff]
  change S.wordCouplingMeasure ν n {z | ¬ |z.2 - z.1| ≤ c ^ n * R} = 0
  have hE : MeasurableSet {z : ℝ × ℝ | ¬ |z.2 - z.1| ≤ c ^ n * R} := by
    have hm : Measurable (fun z : ℝ × ℝ ↦ |z.2 - z.1|) := by fun_prop
    exact (measurableSet_le hm measurable_const).compl
  rw [S.wordCouplingMeasure_apply ν n hE]
  apply Finset.sum_eq_zero
  intro w _
  apply mul_eq_zero_of_right
  apply ae_iff.mp
  filter_upwards [hR] with z hz
  change |S.wordMap n w z - S.wordTranslation n w| ≤ c ^ n * R
  have he : S.wordMap n w z - S.wordTranslation n w = S.wordRatio n w * z := by
    simp only [wordTranslation, wordRatio]
    ring
  rw [he, abs_mul]
  exact mul_le_mul (S.abs_wordRatio_le_pow hc hmax n w) hz (abs_nonneg z) (pow_nonneg hc n)

end ExactOverlaps.SelfSimilar.System
