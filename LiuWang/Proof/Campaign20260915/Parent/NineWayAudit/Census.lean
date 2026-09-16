import Lean

set_option autoImplicit false

namespace LiuWang.Proof.Campaign20260915.Parent.NineWayAudit
open Lean Elab Command

private def emit (fields : List (String × Json)) : CommandElabM Unit :=
  logInfo m!"NINEWAY_JSON {(Json.mkObj fields).compress}"

private def namesJson (names : Array Name) : Json :=
  toJson (names.map Name.toString)

private def kind (ci : ConstantInfo) : String :=
  match ci with
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def member (module : Name) (ci : ConstantInfo) : CommandElabM Unit := do
  let ty ← liftTermElabM do
    withOptions (fun o => o.setBool `pp.all true |>.setNat `pp.maxSteps 10000000) do
      return (← Meta.ppExpr ci.type).pretty 100
  let axioms ← liftCoreM <| collectAxioms ci.name
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "nonstandard axiom in {ci.name}: {ax}"
  emit [("record", toJson "member"), ("module", toJson module.toString),
    ("name", toJson ci.name.toString), ("kind", toJson (kind ci)),
    ("level_params", namesJson ci.levelParams.toArray),
    ("type", toJson ty), ("type_expr", toJson (reprStr ci.type)),
    ("axioms", namesJson axioms)]

/-- Census only the explicitly selected imported ModuleData, never sibling files. -/
def audit (tag : String) (modules roots explicit : Array Name) : CommandElabM Unit := do
  let env ← getEnv
  let mut members : NameSet := {}
  for m in modules do
    let some i := env.header.moduleNames.findIdx? (· == m)
      | throwError "missing audit module {m}"
    let md := env.header.moduleData[i]!
    emit [("record", toJson "module"), ("batch", toJson tag),
      ("module", toJson m.toString), ("count", toJson md.constNames.size)]
    for n in md.constNames do
      let some ci := env.find? n | throwError "missing ModuleData constant {n}"
      members := members.insert n
      member m ci
  for n in explicit do
    unless members.contains n do
      throwError "explicit target absent from selected ModuleData: {n}"
  emit [("record", toJson "explicit_targets"), ("names", namesJson explicit)]
  let mut todo := roots
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | throwError "missing proof-path constant {n}"
    let value := ci.value? (allowOpaque := true)
    let deps := value.map Expr.getUsedConstants |>.getD #[]
    emit [("record", toJson "value"), ("name", toJson n.toString),
      ("kind", toJson (kind ci)), ("allowOpaque", toJson true),
      ("has_value", toJson value.isSome), ("dependencies", namesJson deps)]
    for d in deps do
      if `LiuWang.isPrefixOf d && !seen.contains d then
        todo := todo.push d
  emit [("record", toJson "complete"), ("batch", toJson tag),
    ("modules", toJson modules.size), ("members", toJson members.size),
    ("roots", namesJson roots), ("value_nodes", toJson seen.size)]

end LiuWang.Proof.Campaign20260915.Parent.NineWayAudit
