module

public import ExactOverlaps.SelfSimilar.Definitions

/-!
Every nonempty finite contracting family has an auxiliary uniform
probability system with exactly its original affine maps. Attractor and
no-overlap statements can consequently be stated for unweighted families.
-/

@[expose] public section

open scoped NNReal

namespace ExactOverlaps.SelfSimilar

variable {ι : Type*} [Fintype ι] [Nonempty ι]

noncomputable def uniformSystem (g : ι → RealSimilarity)
    (hg : ∀ i, |(g i).ratio| < 1) : System ι where
  map := g
  contracting := hg
  weight _ := (Fintype.card ι : ℝ≥0)⁻¹
  weight_sum := by
    have hn : (Fintype.card ι : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp [Finset.sum_const, nsmul_eq_mul, hn]

end ExactOverlaps.SelfSimilar
