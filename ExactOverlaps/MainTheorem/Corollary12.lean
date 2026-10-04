/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.MainTheorem.Theorem11
public import ExactOverlaps.SelfSimilar.UnweightedCorollary12

/-!
Corollary 1.2 for an unweighted finite family of contracting similarities.
The dimension formula for the actual nonempty compact invariant set follows
from the proved measure theorem, the Moran probabilities, and cylinder
covers. The no-exact-overlap condition concerns actual affine compositions.
-/

@[expose] public section

open MeasureTheory Set

namespace ExactOverlaps.SelfSimilar

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem corollary_1_2 (g : ι → RealSimilarity) (hg : ∀ i, |(g i).ratio| < 1)
    {s : ℝ} (hs : 0 ≤ s) (hpressure : (∑ i, |(g i).ratio| ^ s) = 1)
    (hfree : HasNoExactOverlaps g) {K : Set ℝ}
    (hK : IsCompact K) (hKn : K.Nonempty) (hKi : K = ⋃ i, (g i) '' K) :
    dimH K = ENNReal.ofReal (min 1 s) :=
  corollary_1_2_of_measure_dimension_formula g hg
    (fun T μ hμ ↦ T.theorem_1_1 μ hμ) hs hpressure hfree hK hKn hKi

end ExactOverlaps.SelfSimilar
