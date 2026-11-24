import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

/- Fail whenever a public or private theorem in the project, including transitive
dependencies, relies on an axiom outside the three standard foundations. -/
elab "#audit_catenary" : command => do
  let env ← getEnv
  let mut checked := 0
  let mut state : Lean.CollectAxioms.State := {}
  for (name, ci) in env.constants.toList do
    let publicName := (Lean.privateToUserName? name).getD name
    if (`Catenary).isPrefixOf publicName then
      match ci with
      | .axiomInfo a =>
        -- The native code generator emits unsafe optimizer specializations.
        -- Kernel proofs cannot depend on these implementation entries.
        unless a.isUnsafe do throwError "unexpected logical axiom in project: {name}"
      | .thmInfo _ =>
        -- Use the same checked kernel environment and traversal as #print axioms.
        -- Reuse its visited set across theorems with shared proof dependencies.
        let (_, next) := ((Lean.CollectAxioms.collect name).run env).run state
        state := next
        for ax in state.axioms do
          unless [`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError "{name} depends on disallowed axiom {ax}"
        checked := checked + 1
      | _ => pure ()
  if checked == 0 then throwError "audit found no theorems"
  logInfo m!"Axiom audit passed for {checked} theorems"

