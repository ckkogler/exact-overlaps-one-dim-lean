module

public import ExactOverlaps.SelfSimilar.Definitions
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
Finite words and their product probability for signed affine systems.
The recursive representation follows Constantin Kogler’s 0BSD
LpSelfSimilar formalization (2026).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace ExactOverlaps.SelfSimilar

universe u

/-- A word of length `n`, represented recursively by its first letter and suffix. -/
def Word (ι : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => ι × Word ι n

instance {ι : Type*} [Fintype ι] (n : ℕ) : Fintype (Word ι n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih => exact inferInstanceAs (Fintype (ι × Word ι n))

namespace System

variable {ι : Type*} [Fintype ι]

/-- Product probability of the letters, including the unused suffix after stopping. -/
noncomputable def wordWeight (S : System ι) : (n : ℕ) → Word ι n → ℝ≥0∞
  | 0, _ => 1
  | n + 1, w => S.weight w.1 * S.wordWeight n w.2

lemma wordWeight_sum (S : System ι) (n : ℕ) : ∑ w, S.wordWeight n w = 1 := by
  induction n with
  | zero => change (∑ _w : PUnit, (1 : ℝ≥0∞)) = 1; simp
  | succ n ih =>
    change (∑ w : ι × Word ι n, (S.weight w.1 : ℝ≥0∞) * S.wordWeight n w.2) = 1
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, ih, mul_one]
    exact S.weight_sum_ennreal


/-- The actual product probability distribution on finite words. -/
noncomputable def wordLaw (S : System ι) (n : ℕ) : PMF (Word ι n) :=
  PMF.ofFintype (S.wordWeight n) (S.wordWeight_sum n)

@[simp] theorem wordLaw_apply (S : System ι) (n : ℕ) (w : Word ι n) :
    S.wordLaw n w = S.wordWeight n w := rfl

/-- The ordered composition associated to a finite word. -/
noncomputable def wordMap (S : System ι) : (n : ℕ) → Word ι n → RealSimilarity
  | 0, _ => RealSimilarity.identity
  | n + 1, w => (S.map w.1).comp (S.wordMap n w.2)

/-- The translation of an ordered random composition. -/
noncomputable def wordTranslation (S : System ι) (n : ℕ) (w : Word ι n) : ℝ :=
  (S.wordMap n w).shift

/-- The signed linear multiplier of an ordered random composition. -/
noncomputable def wordRatio (S : System ι) (n : ℕ) (w : Word ι n) : ℝ :=
  (S.wordMap n w).ratio

@[simp] theorem wordMap_zero (S : System ι) (w : Word ι 0) :
    S.wordMap 0 w = RealSimilarity.identity := rfl

@[simp] theorem wordMap_succ (S : System ι) (n : ℕ) (w : Word ι (n + 1)) :
    S.wordMap (n + 1) w = (S.map w.1).comp (S.wordMap n w.2) := rfl

@[simp] theorem wordRatio_succ (S : System ι) (n : ℕ) (w : Word ι (n + 1)) :
    S.wordRatio (n + 1) w = (S.map w.1).ratio * S.wordRatio n w.2 := rfl

@[simp] theorem wordTranslation_succ (S : System ι) (n : ℕ)
    (w : Word ι (n + 1)) :
    S.wordTranslation (n + 1) w =
      (S.map w.1).ratio * S.wordTranslation n w.2 + (S.map w.1).shift := rfl

theorem wordRatio_ne_zero (S : System ι) (n : ℕ) (w : Word ι n) :
    S.wordRatio n w ≠ 0 := (S.wordMap n w).ratio_ne_zero

/-- Finite iteration of the actual stationarity equation. -/
theorem word_decomposition (S : System ι) {ν : Measure ℝ}
    (hν : S.IsStationary ν) (n : ℕ) {E : Set ℝ} (hE : MeasurableSet E) :
    ν E = ∑ w, S.wordWeight n w * ν ((S.wordMap n w) ⁻¹' E) := by
  induction n generalizing E with
  | zero =>
    change ν E = ∑ _w : PUnit, (1 : ℝ≥0∞) * ν (RealSimilarity.identity ⁻¹' E)
    simp
  | succ n ih =>
    rw [S.stationary_apply hν hE]
    conv_lhs =>
      arg 2
      ext i
      rw [ih (hE.preimage (S.map i).measurable)]
    change (∑ i, (S.weight i : ℝ≥0∞) *
      ∑ w, S.wordWeight n w * ν ((S.wordMap n w) ⁻¹' ((S.map i) ⁻¹' E))) =
      ∑ w : ι × Word ι n, _
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    simp only [wordMap, wordWeight, mul_assoc]
    congr 2
    congr 1
    ext x
    simp only [RealSimilarity.comp_apply, Set.mem_preimage]

end System
end ExactOverlaps.SelfSimilar
