import LiuWang.Proof.Campaign20260915.ZetaWinding.PaidKernelBridge
import LiuWang.Proof.Campaign20260915.ZetaWinding.EndpointBridge
import Lean

set_option autoImplicit false
set_option Elab.async false
set_option pp.fullNames true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for m in env.header.moduleNames do
    if `LiuWang.Proof.Campaign20260915.ZetaWinding.isPrefixOf m then
      let some i := env.header.moduleNames.findIdx? (· == m)
        | throwError "missing imported module {m}"
      let md := env.header.moduleData[i]!
      logInfo m!"WINDING_MODULE|{m}|{md.constNames.size}"
      for n in md.constNames do
        let some ci := env.find? n | throwError "missing module member {n}"
        let kind := match ci with
          | .axiomInfo _ => "axiom"
          | .defnInfo _ => "def"
          | .thmInfo _ => "theorem"
          | .opaqueInfo _ => "opaque"
          | .quotInfo _ => "quot"
          | .inductInfo _ => "inductive"
          | .ctorInfo _ => "constructor"
          | .recInfo _ => "recursor"
        logInfo m!"WINDING_MEMBER|{m}|{n}|{kind}"
        elabCommand (← `(#check @$(mkIdent n)))
        elabCommand (← `(#print axioms $(mkIdent n)))
        if let some value := ci.value? (allowOpaque := true) then
          for dependency in value.getUsedConstants do
            logInfo m!"WINDING_VALUE_EDGE|{n}|{dependency}"
