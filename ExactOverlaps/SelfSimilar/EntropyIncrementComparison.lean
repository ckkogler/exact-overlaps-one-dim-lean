module

public import ExactOverlaps.Entropy.LocalEntropy

/-! Comparing entropy errors at different dyadic levels. -/

@[expose] public section

open MeasureTheory

namespace ExactOverlaps.Entropy

theorem dyadicEntropy_increment_le_int (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ)
    {i j : ℤ} (hij : i ≤ j) :
    dyadicEntropy μ hμ j - dyadicEntropy μ hμ i ≤ ((j - i : ℤ) : ℝ) * Real.log 2 := by
  have hm : ((j - i).toNat : ℤ) = j - i := Int.toNat_of_nonneg (sub_nonneg.mpr hij)
  have h := dyadicEntropy_increment_le μ hμ i (j - i).toNat
  have hj : i + ((j - i).toNat : ℤ) = j := by omega
  have hcast : ((j - i).toNat : ℝ) = ((j - i : ℤ) : ℝ) := by exact_mod_cast hm
  simpa only [hj, hcast] using h

/-- Both entropy increments lie in the same interval, so their difference costs one scale gap. -/
theorem abs_entropy_difference_le_at_lower_scale
    (μ ν : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ) (hν : HasBoundedSupport ν)
    {i j : ℤ} (hij : i ≤ j) :
    |dyadicEntropy μ hμ j - dyadicEntropy ν hν j| ≤
      |dyadicEntropy μ hμ i - dyadicEntropy ν hν i| +
        ((j - i : ℤ) : ℝ) * Real.log 2 := by
  have hμlo := dyadicEntropy_mono μ hμ hij
  have hνlo := dyadicEntropy_mono ν hν hij
  have hμhi := dyadicEntropy_increment_le_int μ hμ hij
  have hνhi := dyadicEntropy_increment_le_int ν hν hij
  have habs₁ := le_abs_self (dyadicEntropy μ hμ i - dyadicEntropy ν hν i)
  have habs₂ := neg_le_abs (dyadicEntropy μ hμ i - dyadicEntropy ν hν i)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end ExactOverlaps.Entropy
