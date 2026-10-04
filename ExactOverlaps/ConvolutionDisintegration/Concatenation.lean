/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.ConvolutionDisintegration.SigmaProducts
public import ExactOverlaps.ConvolutionDisintegration.Admissibility

/-!
# Measurable concatenation of actual convolution factors

Concatenation keeps all factors from both positive finite families. It
convolves their represented laws, adds their variance sums, multiplies their
costs and preserves interval admissibility. All operations are measurable
also when both factor counts vary.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace ExactOverlaps.ConvolutionDisintegration

def prependLaw (μ : ProbabilityMeasure ℝ) (c : FactorFamily) : FactorFamily :=
  ⟨c.1 + 1, (μ, c.2)⟩

lemma measurable_prependLaw :
    Measurable (fun p : ProbabilityMeasure ℝ × FactorFamily ↦ prependLaw p.1 p.2) := by
  apply measurable_from_prod_sigma
  intro n
  exact (measurable_sigma_injection (n + 1)).comp measurable_id

def prependTuple : (n : ℕ) → Entropy.FiniteTuple (ProbabilityMeasure ℝ) n →
    FactorFamily → FactorFamily
  | 0, _, c => c
  | n + 1, w, c => prependLaw w.1 (prependTuple n w.2 c)

def concatenate (c d : FactorFamily) : FactorFamily := prependTuple (c.1 + 1) c.2 d

lemma measurable_prependTuple : ∀ n, Measurable
    (fun p : Entropy.FiniteTuple (ProbabilityMeasure ℝ) n × FactorFamily ↦
      prependTuple n p.1 p.2) := by
  intro n
  induction n with
  | zero => exact measurable_snd
  | succ n ih =>
    exact measurable_prependLaw.comp ((measurable_fst.comp measurable_fst).prodMk
      (ih.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))

lemma measurable_concatenate :
    Measurable (fun p : FactorFamily × FactorFamily ↦ concatenate p.1 p.2) :=
  measurable_from_sigma_prod _ (fun n ↦ measurable_prependTuple (n + 1))

lemma factorCount_prependTuple (n : ℕ)
    (w : Entropy.FiniteTuple (ProbabilityMeasure ℝ) n) (c : FactorFamily) :
    factorCount (prependTuple n w c) = n + factorCount c := by
  induction n with
  | zero => exact (Nat.zero_add _).symm
  | succ n ih =>
    change factorCount (prependTuple n w.2 c) + 1 = n + 1 + factorCount c
    rw [ih w.2]
    omega

lemma factorCount_concatenate (c d : FactorFamily) :
    factorCount (concatenate c d) = factorCount c + factorCount d :=
  factorCount_prependTuple (c.1 + 1) c.2 d

lemma convolutionLaw_prependTuple (n : ℕ)
    (w : Entropy.FiniteTuple (ProbabilityMeasure ℝ) n) (c : FactorFamily) :
    convolutionLaw (prependTuple n w c) =
      Entropy.realConvolution (Entropy.tupleConvolution id n w) (convolutionLaw c) := by
  induction n with
  | zero =>
    exact (Entropy.realConvolution_comm Entropy.zeroRealLaw (convolutionLaw c)).trans
      (Entropy.realConvolution_zero_right (convolutionLaw c)) |>.symm
  | succ n ih =>
    change Entropy.realConvolution w.1 (convolutionLaw (prependTuple n w.2 c)) =
      Entropy.realConvolution (Entropy.realConvolution w.1
        (Entropy.tupleConvolution id n w.2)) (convolutionLaw c)
    rw [ih w.2, Entropy.realConvolution_assoc]

lemma convolutionLaw_concatenate (c d : FactorFamily) :
    convolutionLaw (concatenate c d) =
      Entropy.realConvolution (convolutionLaw c) (convolutionLaw d) :=
  convolutionLaw_prependTuple (c.1 + 1) c.2 d

lemma totalVariance_prependTuple (n : ℕ)
    (w : Entropy.FiniteTuple (ProbabilityMeasure ℝ) n) (c : FactorFamily) :
    totalVariance (prependTuple n w c) =
      Entropy.tupleSum (fun μ : ProbabilityMeasure ℝ ↦ variance (id : ℝ → ℝ) (μ : Measure ℝ))
        n w + totalVariance c := by
  induction n with
  | zero => exact (zero_add _).symm
  | succ n ih =>
    change variance (id : ℝ → ℝ) (w.1 : Measure ℝ) + totalVariance (prependTuple n w.2 c) =
      (variance (id : ℝ → ℝ) (w.1 : Measure ℝ) +
        Entropy.tupleSum (fun μ : ProbabilityMeasure ℝ ↦ variance (id : ℝ → ℝ) (μ : Measure ℝ))
          n w.2) + totalVariance c
    rw [ih w.2, add_assoc]

lemma totalVariance_concatenate (c d : FactorFamily) :
    totalVariance (concatenate c d) = totalVariance c + totalVariance d :=
  totalVariance_prependTuple (c.1 + 1) c.2 d

lemma cost_concatenate (r : ℝ) (c d : FactorFamily) :
    cost r (concatenate c d) = cost r c * cost r d := by
  unfold cost
  rw [totalVariance_concatenate, mul_add, Real.exp_add]

lemma admissible_prependLaw {r : ℝ} {μ : ProbabilityMeasure ℝ} {c : FactorFamily}
    (hμ : HasIntervalWidth μ r) (hc : Admissible r c) : Admissible r (prependLaw μ c) := by
  intro j
  exact Fin.cases hμ hc j

lemma admissible_prependTuple {r : ℝ} (n : ℕ)
    (w : Entropy.FiniteTuple (ProbabilityMeasure ℝ) n) (c : FactorFamily)
    (hw : ∀ i, HasIntervalWidth (Entropy.tupleCoordinate n w i) r)
    (hc : Admissible r c) : Admissible r (prependTuple n w c) := by
  induction n with
  | zero => exact hc
  | succ n ih =>
    exact admissible_prependLaw (hw 0) (ih w.2 (fun j ↦ hw j.succ))

lemma admissible_concatenate {r : ℝ} {c d : FactorFamily}
    (hc : Admissible r c) (hd : Admissible r d) : Admissible r (concatenate c d) :=
  admissible_prependTuple (c.1 + 1) c.2 d hc hd

end ExactOverlaps.ConvolutionDisintegration
