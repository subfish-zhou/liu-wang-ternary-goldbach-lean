import LiuWang.Proof.WeightedLowZeros.Consumer
import Lean

/-! # Exhaustive local declaration, definition-value and transitive-axiom audit -/

set_option autoImplicit false
set_option pp.all true

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let entries := env.constants.toList.filter fun (name, _) =>
    (`LiuWang.Proof.WeightedLowZeros).isPrefixOf name
  if entries.isEmpty then
    throwError "WeightedLowZeros audit found no declarations"
  for (name, info) in entries do
    if info.type.hasSorry then
      throwError "Unproved declaration type: {name}"
    let some value := info.value? true
      | throwError "Declaration without a checked value: {name}"
    if value.hasSorry then
      throwError "Unproved declaration value: {name}"
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Nonstandard transitive axiom in {name}: {axiomName}"
    logInfo m!"DECLARATION {name}\nTYPE {info.type}\nAXIOMS {axioms}"
    match info with
    | .defnInfo _ => logInfo m!"DEFINITION VALUE {name}\n{value}"
    | .thmInfo _ => logInfo m!"PROOF VALUE PRESENT; full expression inspected for sorry: {name}"
    | _ => throwError "Unexpected declaration kind: {name}"
  logInfo m!"AUDITED DECLARATIONS: {entries.length}"
