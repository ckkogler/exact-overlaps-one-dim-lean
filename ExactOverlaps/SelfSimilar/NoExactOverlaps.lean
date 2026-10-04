module

public import ExactOverlaps.SelfSimilar.RandomWalkEntropy
public import ExactOverlaps.SelfSimilar.CodingLaw
public import ExactOverlaps.Entropy.Mixture

/-!
Absence of exact overlaps means that distinct finite words represent
distinct actual affine maps. It implies that every random-walk entropy
is exactly the entropy of the independent letters, with no identifications.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace ExactOverlaps.SelfSimilar.System

open Entropy
variable {ι : Type*} [Fintype ι]

/-- Freeness of the represented finite words, including comparisons of lengths. -/
def HasNoExactOverlaps (S : System ι) : Prop :=
  Function.Injective (fun w : Σ n : ℕ, Word ι n ↦ S.wordMap w.1 w.2)

theorem HasNoExactOverlaps.wordMap_injective {S : System ι}
    (hS : S.HasNoExactOverlaps) (n : ℕ) : Function.Injective (S.wordMap n) := by
  intro v w h
  exact (Sigma.mk.inj_iff.mp (hS (a₁ := ⟨n, v⟩) (a₂ := ⟨n, w⟩) h)).2.eq

noncomputable def alphabetEntropy (S : System ι) : ℝ :=
  finiteEntropy S.alphabetLaw (Set.toFinite _)

theorem alphabetEntropy_eq_sum (S : System ι) :
    S.alphabetEntropy = ∑ i, Real.negMulLog (S.weight i : ℝ) := by
  classical
  rw [alphabetEntropy, finiteEntropy_eq_sum_of_support_subset _ _ Finset.univ
    (fun _ _ ↦ Finset.mem_univ _)]
  simp only [alphabetLaw_apply, ENNReal.coe_toReal]

theorem wordLaw_succ_eq_independent (S : System ι) (n : ℕ) :
    S.wordLaw (n + 1) = independentPair S.alphabetLaw (S.wordLaw n) := by
  apply PMF.ext
  intro w
  change S.wordWeight (n + 1) w = independentPair S.alphabetLaw (S.wordLaw n) (w.1, w.2)
  rw [independentPair_apply]
  rfl

theorem wordLaw_entropy (S : System ι) (n : ℕ) :
    finiteEntropy (S.wordLaw n) (Set.toFinite _) = (n : ℝ) * S.alphabetEntropy := by
  induction n with
  | zero => simp [finiteEntropy, wordLaw_apply, wordWeight]
  | succ n ih =>
    change @finiteEntropy (ι × Word ι n) (S.wordLaw (n + 1)) _ = _
    simp only [S.wordLaw_succ_eq_independent n,
      finiteEntropy_independentPair S.alphabetLaw (S.wordLaw n) (Set.toFinite _) (Set.toFinite _)]
    rw [ih, Nat.cast_add, Nat.cast_one]
    change S.alphabetEntropy + (n : ℝ) * S.alphabetEntropy = _
    ring

theorem jointWordEntropy_eq_of_noExactOverlaps (S : System ι)
    (hS : S.HasNoExactOverlaps) (n : ℕ) :
    S.jointWordEntropy n = (n : ℝ) * S.alphabetEntropy := by
  have hi : Function.Injective (fun w : Word ι n ↦
      (S.wordTranslation n w, S.wordRatio n w)) := by
    intro v w h
    exact hS.wordMap_injective n (RealSimilarity.ext (congrArg Prod.snd h) (congrArg Prod.fst h))
  exact (finiteEntropy_map_of_injective (S.wordLaw n) (Set.toFinite _) hi).trans
    (S.wordLaw_entropy n)

theorem randomWalkEntropyRate_eq_of_noExactOverlaps (S : System ι)
    (hS : S.HasNoExactOverlaps) : S.randomWalkEntropyRate = S.alphabetEntropy := by
  apply tendsto_nhds_unique S.jointWordEntropy_div_tendsto_rate
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [S.jointWordEntropy_eq_of_noExactOverlaps hS n]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  field_simp

end ExactOverlaps.SelfSimilar.System
