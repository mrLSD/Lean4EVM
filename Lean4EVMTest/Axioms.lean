import Lean4EVM

/-!
# Axiom audit

Fails the test build when the library declares an axiom of its own, or when any `Lean4EVM` constant
depends on an axiom other than `propext`, `Classical.choice` and `Quot.sound`. Auditing every kind
of constant, rather than only theorems and definitions, is what makes the first check meaningful:
an axiom that nothing uses, or one reachable only through an `opaque` declaration, is invisible to a
dependency scan of proofs alone.
-/

open Lean Elab Command

/-- Rejects every custom `Lean4EVM` axiom and every `Lean4EVM` constant whose elaboration depends on
an axiom outside the standard three. -/
elab "#audit_axioms" : command => do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut audited : Nat := 0
  for (name, info) in (← getEnv).constants.toList do
    if !(`Lean4EVM).isPrefixOf name || name.isInternal then continue
    audited := audited + 1
    match info with
    | .axiomInfo _ => throwError "{name} is a custom axiom"
    | _ =>
      let bad := (← liftCoreM (collectAxioms name)).filter (· ∉ allowed)
      unless bad.isEmpty do
        throwError "{name} depends on non-standard axioms {bad}"
  logInfo m!"axiom audit: {audited} constants depend only on standard axioms"

#audit_axioms
