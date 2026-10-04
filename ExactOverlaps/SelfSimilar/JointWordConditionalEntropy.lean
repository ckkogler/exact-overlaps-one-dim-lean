module

public import ExactOverlaps.SelfSimilar.JointWordEntropy

/-!
Conditional entropy of the actual joint translation-ratio partition.
Coarsening divides only the dyadic translation label; the signed ratio is
retained exactly, including negative ratios and exact coincidences.
-/

@[expose] public section

namespace ExactOverlaps.SelfSimilar.System

open Entropy
variable {ι : Type*} [Fintype ι]

theorem jointDyadicWordLaw_map_coarse (S : System ι) (n : ℕ) (i : ℤ) (m : ℕ) :
    (S.jointDyadicWordLaw n (i + m)).map (fun z : ℤ × ℝ ↦ (z.1 / (2 ^ m : ℕ), z.2)) =
      S.jointDyadicWordLaw n i := by
  simp only [jointDyadicWordLaw, PMF.map_comp, Function.comp_def]
  congr 1
  funext z
  exact Prod.ext (dyadicQuantize_add_nat i m z.1).symm rfl

/-- The exact conditional entropy for the retained-ratio dyadic partitions.
The source interpretation is supplied below when the coarse level is at most the fine level. -/
noncomputable def jointDyadicWordConditionalEntropy (S : System ι) (n : ℕ) (i f : ℤ) : ℝ :=
  conditionalEntropy (S.jointDyadicWordLaw n f) (S.jointDyadicWordLaw_support_finite n f)
    (fun z : ℤ × ℝ ↦ (z.1 / (2 ^ (f - i).toNat : ℕ), z.2))

theorem jointDyadicWordConditionalEntropy_eq_increment (S : System ι) (n : ℕ)
    {i f : ℤ} (hif : i ≤ f) :
    S.jointDyadicWordConditionalEntropy n i f =
      S.jointDyadicWordEntropy n f - S.jointDyadicWordEntropy n i := by
  have hf : i + ((f - i).toNat : ℤ) = f := by omega
  have hmap := S.jointDyadicWordLaw_map_coarse n i (f - i).toNat
  simp only [hf] at hmap
  simp only [jointDyadicWordConditionalEntropy, conditionalEntropy_eq_entropy_sub, hmap,
    jointDyadicWordEntropy]

theorem jointDyadicWordConditionalEntropy_nonneg (S : System ι) (n : ℕ) (i f : ℤ) :
    0 ≤ S.jointDyadicWordConditionalEntropy n i f :=
  conditionalEntropy_nonneg _ _ _

end ExactOverlaps.SelfSimilar.System
