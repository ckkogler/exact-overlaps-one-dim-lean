module

public import ExactOverlaps.SelfSimilar.Words
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
Adapted from Constantin Kogler’s 0BSD LpSelfSimilar formalization (2026).

Finite first-crossing words give stopped stationary decompositions. Words are
finite products of the alphabet. We index all words at one sufficiently large
depth, but freeze the similarity at its first crossing of the requested scale.
Unused suffixes have total weight one. This permits a direct finite induction
for the stopped decomposition, with no stochastic-process infrastructure.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace ExactOverlaps.SelfSimilar

namespace System

variable {ι : Type*} [Fintype ι]

/-- Starting from `q`, stop at the first ratio at most `t`, or at the available depth. -/
noncomputable def stoppedMap (S : System ι) (t : ℝ) :
    (n : ℕ) → RealSimilarity → Word ι n → RealSimilarity
  | 0, q, _ => q
  | n + 1, q, w => if |q.ratio| ≤ t then q else
      S.stoppedMap t n (q.comp (S.map w.1)) w.2

/-- Finite stopped decomposition. It holds at every depth; scale estimates will
later ensure every branch has crossed the stopping threshold by that depth. -/
lemma stopped_decomposition (S : System ι) {ν : Measure ℝ}
    (hν : S.IsStationary ν) (t : ℝ) (n : ℕ) (q : RealSimilarity)
    {E : Set ℝ} (hE : MeasurableSet E) :
    (∑ w, S.wordWeight n w * ν ((S.stoppedMap t n q w) ⁻¹' E)) = ν (q ⁻¹' E) := by
  induction n generalizing q with
  | zero => change (∑ _w : PUnit, (1 : ℝ≥0∞) * ν (q ⁻¹' E)) = ν (q ⁻¹' E); simp
  | succ n ih =>
    change (∑ w : ι × Word ι n, S.wordWeight (n + 1) w *
      ν ((S.stoppedMap t (n + 1) q w) ⁻¹' E)) = _
    rw [Fintype.sum_prod_type]
    by_cases hq : |q.ratio| ≤ t
    · simp only [wordWeight, stoppedMap, hq, ↓reduceIte]
      simp_rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, S.wordWeight_sum,
        one_mul, S.weight_sum_ennreal]
      rw [one_mul]
    · simp only [wordWeight, stoppedMap, hq, ↓reduceIte]
      simp_rw [mul_assoc, ← Finset.mul_sum, ih]
      rw [S.stationary_apply hν (hE.preimage q.measurable)]
      congr 1
      ext i
      congr 2
      ext x
      simp only [RealSimilarity.comp_apply, Set.mem_preimage]

/-- The lower stopping bound is inherited from the last step before crossing. -/
lemma stoppedMap_ratio_lower (S : System ι) {a t : ℝ}
    (ha : 0 < a) (hmin : ∀ i, a ≤ |(S.map i).ratio|)
    (n : ℕ) (q : RealSimilarity) (hq : a * t < |q.ratio|) (w : Word ι n) :
    a * t < |(S.stoppedMap t n q w).ratio| := by
  induction n generalizing q with
  | zero => exact hq
  | succ n ih =>
    dsimp [stoppedMap]
    split_ifs with hstop
    · exact hq
    · apply ih
      change a * t < |q.ratio * (S.map w.1).ratio|
      rw [abs_mul]
      have hqt : t < |q.ratio| := lt_of_not_ge hstop
      calc
        a * t < a * |q.ratio| := mul_lt_mul_of_pos_left hqt ha
        _ ≤ |q.ratio| * |(S.map w.1).ratio| := by
          rw [mul_comm a]
          exact mul_le_mul_of_nonneg_left (hmin w.1) q.abs_ratio_pos.le

/-- A uniform contraction bound controls the maximum depth needed to cross a scale. -/
lemma stoppedMap_ratio_upper (S : System ι) {c t : ℝ}
    (hc : 0 ≤ c) (hmax : ∀ i, |(S.map i).ratio| ≤ c)
    (n : ℕ) (q : RealSimilarity) (hq : c ^ n * |q.ratio| ≤ t) (w : Word ι n) :
    |(S.stoppedMap t n q w).ratio| ≤ t := by
  induction n generalizing q with
  | zero => simpa [stoppedMap] using hq
  | succ n ih =>
    dsimp [stoppedMap]
    split_ifs with hstop
    · exact hstop
    · apply ih
      calc
        c ^ n * |(q.comp (S.map w.1)).ratio| = c ^ n * (|q.ratio| * |(S.map w.1).ratio|) := by rw [RealSimilarity.comp_ratio, abs_mul]
        _ ≤ c ^ n * (|q.ratio| * c) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hmax w.1) q.abs_ratio_pos.le) (pow_nonneg hc n)
        _ = c ^ (n + 1) * |q.ratio| := by rw [pow_succ]; ring
        _ ≤ t := hq

/-- At every scale in `(0,1)` there is a finite stopped decomposition with all
ratios between `a * t` and `t`. No condition on individual weights is needed. -/
lemma exists_stopped_decomposition (S : System ι) [Nonempty ι]
    {ν : Measure ℝ} (hν : S.IsStationary ν)
    {a t : ℝ} (ha : 0 < a) (ha1 : a < 1) (hmin : ∀ i, a ≤ |(S.map i).ratio|)
    (ht : t ∈ Ioo 0 1) :
    ∃ n : ℕ, ∃ q : Word ι n → RealSimilarity,
      (∀ E, MeasurableSet E → ν E = ∑ w, S.wordWeight n w * ν ((q w) ⁻¹' E)) ∧
      (∀ w, a * t < |(q w).ratio| ∧ |(q w).ratio| ≤ t) := by
  obtain ⟨c, _, hc, hc1, _, hmax, _⟩ := S.exists_uniform_bounds
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one ht.1 hc1
  refine ⟨n, S.stoppedMap t n RealSimilarity.identity, ?_, ?_⟩
  · intro E hE
    simpa only [RealSimilarity.identity_apply, Set.preimage_id'] using
      (S.stopped_decomposition hν t n RealSimilarity.identity hE).symm
  · intro w
    constructor
    · apply S.stoppedMap_ratio_lower ha hmin
      simp only [RealSimilarity.identity, abs_one]
      calc
        a * t < 1 * t := mul_lt_mul_of_pos_right ha1 ht.1
        _ < 1 := by simpa using ht.2
    · apply S.stoppedMap_ratio_upper hc.le hmax
      simpa [RealSimilarity.identity] using hn.le

end System
end ExactOverlaps.SelfSimilar
