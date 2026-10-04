/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Tactic

/-!
# The exact overlaps conjecture for self-similar measures on the real line

We state two main theorems and a corollary from the paper of Samuel Kittle
and Constantin Kogler: the dimension formula for self-similar measures,
its consequence for self-similar sets without exact overlaps, and the
entropy-loss bound for independent finite real random variables.

The definitions below use actual affine compositions and their probability
laws. Elementary probability normalization and finite-support lemmas make
these laws well defined. Ratios can have either sign and can differ between
maps; weights can be zero. Entropies and Lyapunov exponents use natural
logarithms. Two preliminary entropy facts establish subadditivity and
identify the entropy-rate infimum with the random-walk entropy limit.

Measure dimension is the standard lower Hausdorff dimension, defined by
positive-measure Borel sets. The proved library also establishes exact
dimensionality and its identification with this dimension. The corollary
uses the nonempty compact invariant set and the nonnegative Moran root.

Variance energy is the scale integral of normalized local conditional
variance. Its extended nonnegative value is finite for the finite laws
in Theorem 1.3, as proved in the library. The sum law and its finiteness
are conclusions of that theorem, rather than additional assumptions.

The deliberate theorem holes specify independent claims. Solution supplies
their proofs without importing Challenge. Imports here are from Mathlib.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology Classical

namespace ExactOverlaps

/-- An invertible affine similarity with its signed multiplier. -/
structure RealSimilarity where
  ratio : ℝ
  ratio_ne_zero : ratio ≠ 0
  shift : ℝ

namespace RealSimilarity

instance : CoeFun RealSimilarity (fun _ ↦ ℝ → ℝ) :=
  ⟨fun g x ↦ g.ratio * x + g.shift⟩

/-- The identity map x -> x. -/
def identity : RealSimilarity := ⟨1, one_ne_zero, 0⟩

/-- Affine composition, in the order x -> g(h(x)). -/
def comp (g h : RealSimilarity) : RealSimilarity where
  ratio := g.ratio * h.ratio
  ratio_ne_zero := mul_ne_zero g.ratio_ne_zero h.ratio_ne_zero
  shift := g.ratio * h.shift + g.shift

end RealSimilarity

namespace Entropy

/-- Shannon entropy of a finite law, with the convention zero log zero = zero. -/
def finiteEntropy {α : Type*} (p : PMF α) (hp : p.support.Finite) : ℝ :=
  ∑ a ∈ hp.toFinset, Real.negMulLog (p a).toReal

end Entropy

/-- Standard lower Hausdorff dimension of a real Borel measure. -/
def lowerHausdorffDimension (μ : Measure ℝ) : ℝ≥0∞ :=
  ⨅ E : Set ℝ, ⨅ (_ : MeasurableSet E) (_ : 0 < μ E), dimH E

namespace SelfSimilar

/-- A finite family of strict contractions, with probability weights. -/
structure System (ι : Type*) [Fintype ι] where
  map : ι → RealSimilarity
  contracting : ∀ i, |(map i).ratio| < 1
  weight : ι → ℝ≥0
  weight_sum : ∑ i, weight i = 1

universe u

/-- A finite word, represented by its first letter and remaining suffix. -/
def Word (ι : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => ι × Word ι n

instance {ι : Type*} [Fintype ι] (n : ℕ) : Fintype (Word ι n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih => exact inferInstanceAs (Fintype (ι × Word ι n))

namespace System

variable {ι : Type*} [Fintype ι]

/-- The usual weighted pushforward fixed-point equation. -/
def IsStationary (S : System ι) (ν : Measure ℝ) : Prop :=
  ν = ∑ i, (S.weight i : ℝ≥0∞) • ν.map (S.map i)

/-- The probability-weighted logarithm of the absolute contraction ratio. -/
def lyapunov (S : System ι) : ℝ :=
  ∑ i, (S.weight i : ℝ) * Real.log |(S.map i).ratio|

/-- Product of the probabilities of the letters in a word. -/
def wordWeight (S : System ι) : (n : ℕ) → Word ι n → ℝ≥0∞
  | 0, _ => 1
  | n + 1, w => S.weight w.1 * S.wordWeight n w.2

/-- The weights also sum to one as extended nonnegative real numbers. -/
theorem weight_sum_ennreal (S : System ι) :
    ∑ i, (S.weight i : ℝ≥0∞) = 1 := by
  exact_mod_cast S.weight_sum

/-- The independent product weights of all words of a fixed length sum to one. -/
lemma wordWeight_sum (S : System ι) (n : ℕ) : ∑ w, S.wordWeight n w = 1 := by
  induction n with
  | zero => change (∑ _w : PUnit, (1 : ℝ≥0∞)) = 1; simp
  | succ n ih =>
    change (∑ w : ι × Word ι n, (S.weight w.1 : ℝ≥0∞) * S.wordWeight n w.2) = 1
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, ih, mul_one]
    exact S.weight_sum_ennreal

/-- Independent letter weights on all words of length n. -/
def wordLaw (S : System ι) (n : ℕ) : PMF (Word ι n) :=
  PMF.ofFintype (S.wordWeight n) (S.wordWeight_sum n)

/-- Ordered affine composition of the maps named by a word. -/
def wordMap (S : System ι) : (n : ℕ) → Word ι n → RealSimilarity
  | 0, _ => RealSimilarity.identity
  | n + 1, w => (S.map w.1).comp (S.wordMap n w.2)

/-- Translation coordinate of the composed affine map. -/
def wordTranslation (S : System ι) (n : ℕ) (w : Word ι n) : ℝ :=
  (S.wordMap n w).shift

/-- Signed linear multiplier of the composed affine map. -/
def wordRatio (S : System ι) (n : ℕ) (w : Word ι n) : ℝ :=
  (S.wordMap n w).ratio

/-- Coincident affine maps are identified by their translation and signed ratio. -/
def jointWordLaw (S : System ι) (n : ℕ) : PMF (ℝ × ℝ) :=
  (S.wordLaw n).map (fun w ↦ (S.wordTranslation n w, S.wordRatio n w))

/-- A finite word family gives a finitely supported affine random-walk law. -/
theorem jointWordLaw_support_finite (S : System ι) (n : ℕ) :
    (S.jointWordLaw n).support.Finite := by
  rw [jointWordLaw, PMF.support_map]
  exact (Set.toFinite _).image _

/-- Shannon entropy of the actual n-step affine random walk. -/
def jointWordEntropy (S : System ι) (n : ℕ) : ℝ :=
  Entropy.finiteEntropy (S.jointWordLaw n) (S.jointWordLaw_support_finite n)

/-- The subadditivity needed to define the asymptotic random-walk entropy rate. -/
theorem jointWordEntropy_subadditive (S : System ι) : Subadditive S.jointWordEntropy := by
  sorry

/-- The infimum of entropy per step over positive word lengths. -/
def randomWalkEntropyRate (S : System ι) : ℝ :=
  S.jointWordEntropy_subadditive.lim

/-- Preliminary identification with the ordinary asymptotic random-walk entropy. -/
theorem jointWordEntropy_div_tendsto_rate (S : System ι) :
    Tendsto (fun n : ℕ ↦ S.jointWordEntropy n / n) atTop (𝓝 S.randomWalkEntropyRate) := by
  sorry

/-- Theorem 1.1: the dimension formula for every finite contracting real system. -/
theorem theorem_1_1 (S : System ι) (μ : ProbabilityMeasure ℝ)
    (hμ : S.IsStationary (μ : Measure ℝ)) :
    (lowerHausdorffDimension (μ : Measure ℝ)).toReal =
      min 1 (S.randomWalkEntropyRate / |S.lyapunov|) := by
  sorry

end System

set_option bootstrap.genMatcherCode false in
/-- Ordered word composition for an unweighted family of similarities. -/
def composeWord {ι : Type*} (g : ι → RealSimilarity) :
    (n : ℕ) → Word ι n → RealSimilarity
  | 0, _ => RealSimilarity.identity
  | n + 1, w => (g w.1).comp (composeWord g n w.2)

/-- Distinct words of any lengths give distinct actual affine maps. -/
def HasNoExactOverlaps {ι : Type*} (g : ι → RealSimilarity) : Prop :=
  Function.Injective (fun w : Σ n : ℕ, Word ι n ↦ composeWord g w.1 w.2)

/-- Corollary 1.2: the nonempty compact attractor has the expected dimension. -/
theorem corollary_1_2 {ι : Type*} [Fintype ι] [Nonempty ι]
    (g : ι → RealSimilarity) (hg : ∀ i, |(g i).ratio| < 1)
    {s : ℝ} (hs : 0 ≤ s) (hpressure : (∑ i, |(g i).ratio| ^ s) = 1)
    (hfree : HasNoExactOverlaps g) {K : Set ℝ}
    (hK : IsCompact K) (hKn : K.Nonempty) (hKi : K = ⋃ i, (g i) '' K) :
    dimH K = ENNReal.ofReal (min 1 s) := by
  sorry

end SelfSimilar

namespace VarianceEnergy

/-- Squared distance from a center, integrated on the half-open interval [a,a+r). -/
def localQuadraticError (μ : Measure ℝ) (a r c : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Ico a (a + r), ENNReal.ofReal ((x - c) ^ 2) ∂μ

/-- Unnormalized conditional variance, including zero-mass intervals. -/
def localVarianceMass (μ : Measure ℝ) (a r : ℝ) : ℝ≥0∞ :=
  ⨅ c : ℝ, localQuadraticError μ a r c

/-- Average local variance over all interval origins, normalized by 4/r^3. -/
def normalizedLocalVariance (μ : Measure ℝ) (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (4 / r ^ 3) * ∫⁻ a : ℝ, localVarianceMass μ a r

/-- The full variance energy, integrated against dr/r on positive scales. -/
def energy (μ : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ r in Ioi (0 : ℝ), normalizedLocalVariance μ r * ENNReal.ofReal (1 / r)

end VarianceEnergy

namespace Entropy

/-- Theorem 1.3: the original constant 30*m, for actual independent marginal laws. -/
theorem independent_finite_entropy_loss_exists {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : ℕ) (X : Fin m → Ω → ℝ)
    (hXm : ∀ i, AEMeasurable (X i) μ) (hXi : iIndepFun X μ)
    (p : Fin m → PMF ℝ) (hp : ∀ i, (p i).support.Finite)
    (hLaw : ∀ i, μ.map (X i) = (p i).toMeasure) :
    ∃ (q : PMF ℝ) (hq : q.support.Finite),
      μ.map (fun ω ↦ ∑ i, X i ω) = q.toMeasure ∧
      (∑ i, finiteEntropy (p i) (hp i)) - finiteEntropy q hq ≤
        30 * m * ∑ i, (VarianceEnergy.energy (μ.map (X i))).toReal := by
  sorry

end Entropy
end ExactOverlaps
