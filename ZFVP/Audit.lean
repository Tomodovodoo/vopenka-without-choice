import ZFVP
import Lean.Util.CollectAxioms
import Lean.Elab.Print

/-! Audit every declaration exported under the project's mathematical namespace.
This command inspects proof terms; it does not introduce any mathematical facts.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants do
    let projectModule := match env.getModuleIdxFor? name with
      | some idx => (`ZFVP).isPrefixOf (env.header.moduleNames.getD idx.toNat .anonymous)
      | none => false
    if (`ZFVP).isPrefixOf name || projectModule then
      let axs ← collectAxioms name
      for ax in axs do
        unless allowed.contains ax do
          throwError "Forbidden axiom {ax} in {name}"
      elabCommand (← `(command| #print axioms $(mkIdent name)))
      count := count + 1
  unless count > 0 do
    throwError "No project declarations found; an empty audit is not success"
  logInfo m!"Audited {count} project declarations against the foundational allowlist."
