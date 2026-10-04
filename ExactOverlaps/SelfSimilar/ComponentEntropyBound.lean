module

public import ExactOverlaps.SelfSimilar.SignedTailNormalization
public import ExactOverlaps.SelfSimilar.OneSidedComponents

/-!
The inverse gain bounds the mean entropy of the translation components by
their mean excess convolution entropy. The expectation uses actual cell
probabilities, and the dyadic boundary error is explicit.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators

namespace ExactOverlaps.SelfSimilar.System

open Entropy
variable {ι : Type*} [Fintype ι]

theorem exists_average_component_entropy_bound (S : System ι) (μ : ProbabilityMeasure ℝ)
    (hμ : S.IsStationary (μ : Measure ℝ))
    (hdim : (lowerHausdorffDimension (μ : Measure ℝ)).toReal < 1)
    {e : ℝ} (he : 0 < e) :
    ∃ γ > 0, ∃ N : ℕ, 0 < N ∧ ∀ m : ℕ, N ≤ m →
      ∀ (g : RealSimilarity) (i : ℤ) (ν : ProbabilityMeasure ℝ) (hν : HasBoundedSupport ν),
      (1 / 2 : ℝ) ≤ (2 : ℝ) ^ i * |g.ratio| → (2 : ℝ) ^ i * |g.ratio| ≤ 1 → g.shift = 0 →
      γ * averageRawComponentEntropy ν hν i m ≤ γ * e * ((m : ℝ) * Real.log 2) +
        averageRawLeftConvolutionEntropy ν (μ.map g) hν
          (g.hasBoundedSupport_map μ (S.hasBoundedSupport hμ)) i m -
        dyadicEntropy (μ.map g) (g.hasBoundedSupport_map μ (S.hasBoundedSupport hμ)) (i + m) +
        Real.log 2 := by
  obtain ⟨γ, hγ, N, hN, hgain⟩ := S.exists_component_entropy_gain μ hμ hdim he
  refine ⟨γ, hγ, N, hN, ?_⟩
  intro m hm g i ν hν hratioLo hratioHi hshift
  let : Fintype (dyadicLaw ν i).support := (dyadicLaw_support_finite ν hν i).fintype
  let H (k : (dyadicLaw ν i).support) :=
    dyadicEntropy (rawComponent ν i k) (rawComponent_hasBoundedSupport ν i k) (i + m)
  let G (k : (dyadicLaw ν i).support) :=
    dyadicEntropy (realConvolution (rawComponent ν i k) (μ.map g))
      (realConvolution_hasBoundedSupport _ _ (rawComponent_hasBoundedSupport ν i k)
        (g.hasBoundedSupport_map μ (S.hasBoundedSupport hμ))) (i + m)
  let T := dyadicEntropy (μ.map g) (g.hasBoundedSupport_map μ (S.hasBoundedSupport hμ)) (i + m)
  let D : ℝ := (m : ℝ) * Real.log 2
  have hD : 0 < D := mul_pos (Nat.cast_pos.mpr (lt_of_lt_of_le hN hm)) (Real.log_pos (by norm_num))
  have hpoint (k : (dyadicLaw ν i).support) : γ * H k ≤ γ * e * D + G k - T + Real.log 2 := by
    have hupper : H k ≤ D := by
      have h := dyadicEntropy_le_nat_mul_log_two (rescaledComponent ν i k)
        (rescaledComponent_hasBoundedSupport ν i k) m (ae_rescaledComponent_mem_Ico ν i k)
      simpa only [dyadicEntropy_rescaledComponent] using h
    have hmono : T ≤ G k + Real.log 2 :=
      dyadicEntropy_right_le_convolution_add_log_two (rawComponent ν i k) (μ.map g)
        (rawComponent_hasBoundedSupport ν i k) (g.hasBoundedSupport_map μ (S.hasBoundedSupport hμ)) (i + m)
    by_cases hsmall : H k ≤ e * D
    · have h := mul_le_mul_of_nonneg_left hsmall hγ.le
      nlinarith
    · have hent : e < H k / D := (lt_div_iff₀ hD).mpr (lt_of_not_ge hsmall)
      have hg := hgain m hm g i ν k hratioLo hratioHi hshift hent
      have hg' : T + γ * D ≤ G k := by
        simpa only [realConvolution_comm (μ.map g) (rawComponent ν i k)] using hg
      have h := mul_le_mul_of_nonneg_left hupper hγ.le
      nlinarith [mul_nonneg (mul_nonneg hγ.le he.le) hD.le,
        Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  have hav := Finset.sum_le_sum (s := Finset.univ) (fun k _ ↦
    mul_le_mul_of_nonneg_left (hpoint k)
      (show 0 ≤ ((dyadicLaw ν i) k).toReal from ENNReal.toReal_nonneg))
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, sum_dyadic_cell_mass ν hν i, one_mul] at hav
  have heq : (∑ k : (dyadicLaw ν i).support, ((dyadicLaw ν i) k).toReal * (γ * H k)) =
      γ * averageRawComponentEntropy ν hν i m := by
    unfold averageRawComponentEntropy
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [heq] at hav
  exact hav

end ExactOverlaps.SelfSimilar.System
