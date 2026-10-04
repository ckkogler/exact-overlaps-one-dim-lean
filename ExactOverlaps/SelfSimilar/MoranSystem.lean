module

public import ExactOverlaps.SelfSimilar.SimilarityDimension
public import ExactOverlaps.SelfSimilar.NoExactOverlaps
public import ExactOverlaps.SelfSimilar.AttractorUniqueness

/-!
Moran weights on the original signed affine maps form a genuine probability
system. Its letter entropy divided by the absolute Lyapunov exponent is
the similarity dimension; absence of exact overlaps makes this also the
actual random-walk entropy ratio.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι]

noncomputable def moranWeight (S : System ι) (s : ℝ) (i : ι) : ℝ≥0 :=
  Real.toNNReal (|(S.map i).ratio| ^ s)

theorem moranWeight_coe (S : System ι) (s : ℝ) (i : ι) :
    (S.moranWeight s i : ℝ) = |(S.map i).ratio| ^ s :=
  Real.coe_toNNReal _ (Real.rpow_nonneg (abs_nonneg _) _)

noncomputable def moranSystem (S : System ι) (s : ℝ) (hs : S.pressure s = 1) : System ι where
  map := S.map
  contracting := S.contracting
  weight := S.moranWeight s
  weight_sum := by
    apply NNReal.eq
    rw [NNReal.coe_sum]
    simp only [S.moranWeight_coe, NNReal.coe_one]
    exact hs

theorem wordMap_eq_of_map_eq (S T : System ι) (h : S.map = T.map) (n : ℕ) (w : Word ι n) :
    S.wordMap n w = T.wordMap n w := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [wordMap_succ, h, ih]

theorem moranSystem_noExactOverlaps (S : System ι) {s : ℝ} (hs : S.pressure s = 1)
    (hS : S.HasNoExactOverlaps) : (S.moranSystem s hs).HasNoExactOverlaps := by
  intro v w he
  apply hS
  simpa only [wordMap_eq_of_map_eq (S.moranSystem s hs) S rfl] using he

theorem moranSystem_attractor (S : System ι) {s : ℝ} (hs : S.pressure s = 1) :
    (S.moranSystem s hs).attractor = S.attractor := by
  apply S.eq_attractor_of_compact_invariant
    (S.moranSystem s hs).attractor_isCompact (S.moranSystem s hs).attractor_nonempty
  exact (S.moranSystem s hs).attractor_eq_union

theorem moranSystem_alphabetEntropy (S : System ι) {s : ℝ} (hs : S.pressure s = 1) :
    (S.moranSystem s hs).alphabetEntropy = s * |(S.moranSystem s hs).lyapunov| := by
  rw [alphabetEntropy_eq_sum, abs_lyapunov_eq_neg]
  simp only [lyapunov, moranSystem, moranWeight_coe]
  change (∑ i, Real.negMulLog (|(S.map i).ratio| ^ s)) =
    s * -(∑ i, |(S.map i).ratio| ^ s * Real.log |(S.map i).ratio|)
  simp only [Real.negMulLog, Real.log_rpow (S.map _).abs_ratio_pos]
  rw [← Finset.sum_neg_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem moranSystem_entropyRate_div_lyapunov (S : System ι) {s : ℝ}
    (hs : S.pressure s = 1) (hS : S.HasNoExactOverlaps) :
    (S.moranSystem s hs).randomWalkEntropyRate / |(S.moranSystem s hs).lyapunov| = s := by
  rw [randomWalkEntropyRate_eq_of_noExactOverlaps _ (S.moranSystem_noExactOverlaps hs hS),
    S.moranSystem_alphabetEntropy hs]
  exact mul_div_cancel_right₀ s (S.moranSystem s hs).abs_lyapunov_pos.ne'

end ExactOverlaps.SelfSimilar.System
