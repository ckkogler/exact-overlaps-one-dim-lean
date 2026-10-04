/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.WordOperations

/-! The actual product law of a finite prefix and its fresh finite suffix. -/

@[expose] public section

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι]

theorem wordLaw_map_split (S : System ι) (n m : ℕ) :
    (S.wordLaw (m + n)).map (Word.split n m) =
      Entropy.independentPair (S.wordLaw n) (S.wordLaw m) := by
  apply PMF.ext
  rintro ⟨w, v⟩
  have h := Entropy.map_apply_of_injective (S.wordLaw (m + n))
    (Word.appendEquiv (ι := ι) n m).symm.injective (Word.append n m w v)
  change ((S.wordLaw (m + n)).map (Word.split n m))
    (Word.split n m (Word.append n m w v)) = _ at h
  rw [Word.split_append] at h
  rw [h, Entropy.independentPair_apply]
  exact S.wordWeight_append n m w v

theorem independent_wordLaw_map_append (S : System ι) (n m : ℕ) :
    (Entropy.independentPair (S.wordLaw n) (S.wordLaw m)).map
      (fun z ↦ Word.append n m z.1 z.2) = S.wordLaw (m + n) := by
  rw [← S.wordLaw_map_split n m, PMF.map_comp]
  have h : (fun z : Word ι (m + n) ↦
      Word.append n m (Word.split n m z).1 (Word.split n m z).2) = id :=
    funext (Word.append_split n m)
  change (S.wordLaw (m + n)).map
    (fun z ↦ Word.append n m (Word.split n m z).1 (Word.split n m z).2) = _
  rw [h, PMF.map_id]

theorem wordLaw_map_prefix (S : System ι) (n m : ℕ) :
    (S.wordLaw (m + n)).map (fun w ↦ (Word.split n m w).1) = S.wordLaw n := by
  rw [← Function.comp_def, ← PMF.map_comp, S.wordLaw_map_split,
    Entropy.independentPair_map_fst]

theorem wordLaw_map_suffix (S : System ι) (n m : ℕ) :
    (S.wordLaw (m + n)).map (fun w ↦ (Word.split n m w).2) = S.wordLaw m := by
  rw [← Function.comp_def, ← PMF.map_comp, S.wordLaw_map_split,
    Entropy.independentPair_map_snd]

end ExactOverlaps.SelfSimilar.System
