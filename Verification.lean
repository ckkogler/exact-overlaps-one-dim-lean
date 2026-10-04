/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

import Solution
import Lean

/-!
Audit every imported declaration originating in the authored library,
including definitions, instances and generated declarations. The audit
uses Lean's recorded transitive axiom dependencies and fails on any axiom
outside the three permitted logical axioms. Challenge is not imported.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let names := env.constants.fold (init := #[]) fun acc name _ =>
    match env.getModuleIdxFor? name with
    | none => acc
    | some idx =>
      if (`ExactOverlaps).isPrefixOf env.header.moduleNames[idx]! then acc.push name else acc
  if names.isEmpty then throwError "The authored proof library was not imported."
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for name in names.qsort Name.lt do
    let axioms ← collectAxioms name
    let unexpected := axioms.filter fun ax => !allowed.contains ax
    unless unexpected.isEmpty do
      throwError "Forbidden axioms in {name}: {unexpected}"
    logInfo m!"AXIOM_AUDIT {name}: {axioms}"
  logInfo m!"AXIOM_AUDIT_PASS {names.size} authored declarations"

#check ExactOverlaps.SelfSimilar.System.jointWordEntropy_div_tendsto_rate
#check ExactOverlaps.SelfSimilar.System.theorem_1_1
#check ExactOverlaps.SelfSimilar.corollary_1_2
#check ExactOverlaps.Entropy.independent_finite_entropy_loss_exists
#check ExactOverlaps.SelfSimilar.System.hochman_theorem_1_4
