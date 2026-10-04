/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.StoppingRules
public import ExactOverlaps.Entropy.Finite

/-! Choosing continuations on a finite positive support gives a genuine common time bound. -/

@[expose] public section

open scoped Classical

namespace ExactOverlaps.StoppedConcatenation

variable {ι α : Type*} [MeasurableSpace ι]

noncomputable def supportedRule (p : PMF α) (U : p.support → BoundedStoppingRule ι)
    (a : α) : BoundedStoppingRule ι :=
  if ha : a ∈ p.support then U ⟨a, ha⟩ else BoundedStoppingRule.constant 0

theorem supportedRule_at (p : PMF α) (U : p.support → BoundedStoppingRule ι)
    (a : p.support) : supportedRule p U a = U a := by
  simp [supportedRule, a.property]

noncomputable def supportedRuleHorizon (p : PMF α) (hp : p.support.Finite)
    (U : p.support → BoundedStoppingRule ι) : ℕ :=
  letI : Fintype p.support := hp.fintype
  ∑ a : p.support, (U a).horizon

theorem supportedRule_horizon_le (p : PMF α) (hp : p.support.Finite)
    (U : p.support → BoundedStoppingRule ι) (a : α) :
    (supportedRule p U a).horizon ≤ supportedRuleHorizon p hp U := by
  let : Fintype p.support := hp.fintype
  unfold supportedRule
  split_ifs with ha
  · change (U ⟨a, ha⟩).horizon ≤ ∑ b : p.support, (U b).horizon
    exact Finset.single_le_sum (f := fun b : p.support ↦ (U b).horizon) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ (⟨a, ha⟩ : p.support))
  · exact Nat.zero_le _

end ExactOverlaps.StoppedConcatenation
