/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.FiniteWJensen
public import ExactOverlaps.SelfSimilar.ConditionalFunctionalTower
public import ExactOverlaps.Entropy.ConditionalConcavity

/-! W convexity and coarsening for genuine finite conditional laws of real statistics. -/

@[expose] public section

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace ExactOverlaps.ConvolutionDisintegration

open Entropy FiniteProbability

def pmfLaw {α : Type*} [MeasurableSpace α] (p : PMF α) : ProbabilityMeasure α :=
  ⟨p.toMeasure, inferInstance⟩

theorem finiteMix_pmfLaw_bind {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (p : PMF ι) (q : ι → PMF α) :
    finiteMix p (fun i ↦ pmfLaw (q i)) = pmfLaw (p.bind q) := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext
  intro E hE
  change (∑ i, p i • (q i).toMeasure) E = (p.bind q).toMeasure E
  rw [PMF.toMeasure_bind_apply _ _ _ hE, tsum_fintype, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]

theorem W_bind_le {ι : Type*} [Fintype ι] (p : PMF ι) (q : ι → PMF ℝ)
    {r : ℝ} (hr : 0 ≤ r) :
    W (pmfLaw (p.bind q)) r ≤ ∑ i, (p i).toReal * W (pmfLaw (q i)) r := by
  have h := W_finiteMix_le p (fun i ↦ pmfLaw (q i)) hr
  rwa [finiteMix_pmfLaw_bind] at h

def meanConditionalMapW {α β : Type*} (p : PMF α) (hp : p.support.Finite)
    (f : α → β) (B : α → ℝ) (r : ℝ) : ℝ :=
  meanFiberFunctional p hp f (fun q _ ↦ W (pmfLaw (q.map B)) r)

theorem W_le_meanConditionalMapW {α β : Type*} (p : PMF α) (hp : p.support.Finite)
    (f : α → β) (B : α → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    W (pmfLaw (p.map B)) r ≤ meanConditionalMapW p hp f B r := by
  let : Fintype (p.map f).support := (show (p.map f).support.Finite from by
    simpa using hp.image f).fintype
  have he : (supportLaw (p.map f)).bind (fun b ↦ (conditionalPMF p f b).map B) = p.map B := by
    rw [← PMF.map_bind, bind_conditionalPMF p hp f]
  have h := W_bind_le (supportLaw (p.map f)) (fun b ↦ (conditionalPMF p f b).map B) hr
  rw [he] at h
  rw [meanConditionalMapW, meanFiberFunctional_eq_sum]
  exact h

theorem meanConditionalMapW_coarsening_le {α β γ : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (k : β → γ) (B : α → ℝ)
    {r : ℝ} (hr : 0 ≤ r) :
    meanConditionalMapW p hp (fun a ↦ k (f a)) B r ≤ meanConditionalMapW p hp f B r := by
  let F : (q : PMF α) → q.support.Finite → ℝ := fun q _ ↦ W (pmfLaw (q.map B)) r
  have hconcave (q : PMF α) (hq : q.support.Finite) :
      meanFiberFunctional q hq f (fun u hu ↦ (-1 : ℝ) * F u hu) ≤ (-1 : ℝ) * F q hq := by
    rw [meanFiberFunctional_const_mul]
    have h := W_le_meanConditionalMapW q hq f B hr
    change F q hq ≤ meanFiberFunctional q hq f F at h
    linarith
  have h := meanFiberFunctional_refinement_le p hp f k (fun q hq ↦ (-1 : ℝ) * F q hq) hconcave
  rw [meanFiberFunctional_const_mul, meanFiberFunctional_const_mul] at h
  change meanFiberFunctional p hp (fun a ↦ k (f a)) F ≤ meanFiberFunctional p hp f F
  linarith

end ExactOverlaps.ConvolutionDisintegration
