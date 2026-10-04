module

public import ExactOverlaps.SelfSimilar.WordBounds
public import ExactOverlaps.StoppedConcatenation.WordLaws
public import Mathlib.Analysis.Subadditive

/-!
The standard entropy rate of the actual affine random walk. Concatenation
gives subadditivity; Fekete's lemma identifies the infimum with the limit.
Coincident affine maps are identified by their actual translation and ratio.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace ExactOverlaps.SelfSimilar.System

open Entropy
variable {ι : Type*} [Fintype ι]

def composeAffineCoordinates (z : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ × ℝ :=
  (z.1.1 + z.1.2 * z.2.1, z.1.2 * z.2.2)

theorem jointWordLaw_add (S : System ι) (n m : ℕ) :
    (independentPair (S.jointWordLaw n) (S.jointWordLaw m)).map composeAffineCoordinates =
      S.jointWordLaw (m + n) := by
  have hmap : independentPair (S.jointWordLaw n) (S.jointWordLaw m) =
      (independentPair (S.wordLaw n) (S.wordLaw m)).map
        (fun z ↦ ((S.wordTranslation n z.1, S.wordRatio n z.1),
          (S.wordTranslation m z.2, S.wordRatio m z.2))) := by
    unfold jointWordLaw
    rw [← independentPair_map_right, ← independentPair_map_left, PMF.map_comp]
    rfl
  rw [hmap, PMF.map_comp]
  unfold jointWordLaw
  rw [← S.independent_wordLaw_map_append n m, PMF.map_comp]
  congr 1
  funext z
  dsimp [Function.comp_def, wordTranslation, wordRatio]
  rw [S.wordMap_append]
  apply Prod.ext
  · exact add_comm _ _
  · rfl

noncomputable def jointWordEntropy (S : System ι) (n : ℕ) : ℝ :=
  finiteEntropy (S.jointWordLaw n) (S.jointWordLaw_support_finite n)

theorem jointWordEntropy_nonneg (S : System ι) (n : ℕ) : 0 ≤ S.jointWordEntropy n :=
  finiteEntropy_nonneg _ _

theorem jointWordEntropy_subadditive (S : System ι) : Subadditive S.jointWordEntropy := by
  intro m n
  have h := finiteEntropy_map_le (independentPair (S.jointWordLaw n) (S.jointWordLaw m))
    (independentPair_support_finite _ _ (S.jointWordLaw_support_finite n)
      (S.jointWordLaw_support_finite m)) composeAffineCoordinates
  simp only [S.jointWordLaw_add,
    finiteEntropy_independentPair (S.jointWordLaw n) (S.jointWordLaw m)
      (S.jointWordLaw_support_finite n) (S.jointWordLaw_support_finite m)] at h
  simpa only [jointWordEntropy, add_comm] using h

theorem jointWordEntropy_div_bddBelow (S : System ι) :
    BddBelow (range (fun n : ℕ ↦ S.jointWordEntropy n / n)) := by
  refine ⟨0, ?_⟩
  rintro x ⟨n, rfl⟩
  exact div_nonneg (S.jointWordEntropy_nonneg n) (Nat.cast_nonneg n)

/-- Standard asymptotic Shannon entropy of the affine random walk, in natural units. -/
noncomputable def randomWalkEntropyRate (S : System ι) : ℝ :=
  S.jointWordEntropy_subadditive.lim

theorem jointWordEntropy_div_tendsto_rate (S : System ι) :
    Tendsto (fun n : ℕ ↦ S.jointWordEntropy n / n) atTop (𝓝 S.randomWalkEntropyRate) :=
  S.jointWordEntropy_subadditive.tendsto_lim S.jointWordEntropy_div_bddBelow

theorem randomWalkEntropyRate_nonneg (S : System ι) : 0 ≤ S.randomWalkEntropyRate :=
  le_of_tendsto_of_tendsto' tendsto_const_nhds S.jointWordEntropy_div_tendsto_rate
    (fun n ↦ div_nonneg (S.jointWordEntropy_nonneg n) (Nat.cast_nonneg n))

theorem mul_randomWalkEntropyRate_le (S : System ι) (n : ℕ) :
    (n : ℝ) * S.randomWalkEntropyRate ≤ S.jointWordEntropy n := by
  by_cases hn : n = 0
  · simpa only [hn, Nat.cast_zero, zero_mul] using S.jointWordEntropy_nonneg 0
  · have h := S.jointWordEntropy_subadditive.lim_le_div S.jointWordEntropy_div_bddBelow hn
    have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    simpa only [randomWalkEntropyRate, mul_comm] using (le_div_iff₀ hn').mp h

end ExactOverlaps.SelfSimilar.System
