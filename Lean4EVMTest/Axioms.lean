import Lean4EVM

/-!
# Axiom audit

Fails the test build when any `Lean4EVM` declaration depends on an axiom other than `propext`,
`Classical.choice`, and `Quot.sound`, so compiler-trusting or unfinished proofs cannot enter the
library unnoticed.
-/

open Lean Elab Command

/-- Rejects every `Lean4EVM` theorem or definition whose proof depends on a non-standard axiom. -/
elab "#audit_axioms" : command => do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut audited : Nat := 0
  for (name, info) in (← getEnv).constants.toList do
    let isDeclaration := match info with
      | .thmInfo _ | .defnInfo _ => true
      | _ => false
    if (`Lean4EVM).isPrefixOf name && !name.isInternal && isDeclaration then
      audited := audited + 1
      let bad := (← liftCoreM (collectAxioms name)).filter (· ∉ allowed)
      unless bad.isEmpty do
        throwError "{name} depends on non-standard axioms {bad}"
  logInfo m!"axiom audit: {audited} declarations depend only on standard axioms"

#audit_axioms
