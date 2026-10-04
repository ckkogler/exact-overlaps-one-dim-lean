/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.ConvolutionDisintegration.LawOperations
public import ExactOverlaps.Entropy.TupleConvolution

/-!
# A measurable space of finite positive convolution families

The countable disjoint union retains every positive finite number of factors.
Each factor is an actual real probability law. Convolution, total variance,
factor count and the exponential cost are proved measurable on this space.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory

namespace ExactOverlaps.ConvolutionDisintegration

instance finiteTupleMeasurableSpace (α : Type*) [MeasurableSpace α] :
    (n : ℕ) → MeasurableSpace (Entropy.FiniteTuple α n)
  | 0 => inferInstanceAs (MeasurableSpace PUnit)
  | n + 1 => by
      letI := finiteTupleMeasurableSpace α n
      exact inferInstanceAs (MeasurableSpace (α × Entropy.FiniteTuple α n))

lemma measurable_from_sigma {ι : Type*} {A : ι → Type*}
    [∀ i, MeasurableSpace (A i)] {B : Type*} [MeasurableSpace B]
    (f : (Σ i, A i) → B) (hf : ∀ i, Measurable (fun x ↦ f ⟨i, x⟩)) : Measurable f := by
  intro E hE
  change MeasurableSet[⨅ i, (inferInstance : MeasurableSpace (A i)).map (Sigma.mk i)] (f ⁻¹' E)
  rw [MeasurableSpace.measurableSet_iInf]
  intro i
  exact hf i hE

lemma measurable_sigma_injection {ι : Type*} {A : ι → Type*}
    [∀ i, MeasurableSpace (A i)] (i : ι) : Measurable (Sigma.mk i : A i → Sigma A) := by
  intro E hE
  change MeasurableSet[⨅ j, (inferInstance : MeasurableSpace (A j)).map (Sigma.mk j)] E at hE
  exact MeasurableSpace.measurableSet_iInf.mp hE i

lemma measurable_tupleConvolution {α : Type*} [MeasurableSpace α]
    (ν : α → ProbabilityMeasure ℝ) (hν : Measurable ν) :
    ∀ n, Measurable (Entropy.tupleConvolution ν n) := by
  intro n
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact measurable_convolution.comp
      ((hν.comp measurable_fst).prodMk (ih.comp measurable_snd))

lemma measurable_tupleSum {α : Type*} [MeasurableSpace α]
    (f : α → ℝ) (hf : Measurable f) : ∀ n, Measurable (Entropy.tupleSum f n) := by
  intro n
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact (hf.comp measurable_fst).add (ih.comp measurable_snd)

abbrev FactorFamily := Σ n : ℕ, Entropy.FiniteTuple (ProbabilityMeasure ℝ) (n + 1)

def factorCount (c : FactorFamily) : ℕ := c.1 + 1

def convolutionLaw (c : FactorFamily) : ProbabilityMeasure ℝ :=
  Entropy.tupleConvolution id (c.1 + 1) c.2

def totalVariance (c : FactorFamily) : ℝ :=
  Entropy.tupleSum (fun μ : ProbabilityMeasure ℝ ↦ variance (id : ℝ → ℝ) (μ : Measure ℝ))
    (c.1 + 1) c.2

def cost (r : ℝ) (c : FactorFamily) : ℝ := Real.exp (-4 / r ^ 2 * totalVariance c)

lemma factorCount_pos (c : FactorFamily) : 0 < factorCount c := Nat.zero_lt_succ _

lemma measurable_factorCount : Measurable factorCount := by
  apply measurable_from_sigma
  intro n
  change Measurable (fun _ : Entropy.FiniteTuple (ProbabilityMeasure ℝ) (n + 1) ↦ n + 1)
  exact measurable_const

lemma measurable_convolutionLaw : Measurable convolutionLaw :=
  measurable_from_sigma convolutionLaw (fun n ↦ measurable_tupleConvolution id measurable_id (n + 1))

lemma measurable_totalVariance : Measurable totalVariance :=
  measurable_from_sigma totalVariance (fun n ↦ measurable_tupleSum _ measurable_variance (n + 1))

lemma totalVariance_nonneg (c : FactorFamily) : 0 ≤ totalVariance c := by
  have h : ∀ n (w : Entropy.FiniteTuple (ProbabilityMeasure ℝ) n),
      0 ≤ Entropy.tupleSum (fun μ : ProbabilityMeasure ℝ ↦
        variance (id : ℝ → ℝ) (μ : Measure ℝ)) n w := by
    intro n
    induction n with
    | zero => intro _; exact le_rfl
    | succ n ih => intro w; exact add_nonneg (variance_nonneg _ _) (ih w.2)
  exact h (c.1 + 1) c.2

lemma measurable_cost (r : ℝ) : Measurable (cost r) :=
  Real.measurable_exp.comp (measurable_const.mul measurable_totalVariance)

lemma cost_pos (r : ℝ) (c : FactorFamily) : 0 < cost r c := Real.exp_pos _

lemma cost_le_one (r : ℝ) (c : FactorFamily) : cost r c ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg
    (div_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg r)) (totalVariance_nonneg c)

end ExactOverlaps.ConvolutionDisintegration
