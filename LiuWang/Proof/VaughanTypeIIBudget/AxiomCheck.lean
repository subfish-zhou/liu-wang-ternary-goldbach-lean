import LiuWang.Proof.VaughanTypeIIBudget.Consumer
import LiuWang.Proof.VaughanTypeIIBudget.KernelBridge
import Lean.Util.CollectAxioms

/-! 全部新增声明的完整类型和传递公理；拒绝非标准公理。 -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let ns := `LiuWang.Proof.VaughanTypeIIBudget
  let declarations := env.constants.toList.filter fun (name, _) =>
    ns.isPrefixOf name || name.toString.startsWith "_private.LiuWang.Proof.VaughanTypeIIBudget."
  for (name, info) in declarations do
    let axioms ← liftCoreM (Lean.collectAxioms name)
    let unexpected := axioms.filter fun ax =>
      !(#[`propext, `Classical.choice, `Quot.sound].contains ax)
    unless unexpected.isEmpty do
      throwError "Nonstandard axioms in {name}: {unexpected}"
    let type ← liftTermElabM <| withOptions
      (fun opts => (opts.setBool `pp.universes true).setBool `pp.fullNames true)
      (Lean.Meta.ppExpr info.type)
    let row := Json.mkObj [
      ("name", toJson name.toString),
      ("type", toJson type.pretty),
      ("axioms", toJson (axioms.map Name.toString)),
      ("nonstandard_axioms", toJson (unexpected.map Name.toString))]
    logInfo m!"TYPEII_BUDGET_AUDIT {row.compress}"

set_option pp.all true in
#print LiuWang.Proof.VaughanTypeIIBudget.scalarRowBudget
set_option pp.all true in
#print LiuWang.Proof.VaughanTypeIIBudget.scalarDyadicBudget
set_option pp.all true in
#print LiuWang.Proof.VaughanTypeIIBudget.termA
set_option pp.all true in
#print LiuWang.Proof.VaughanTypeIIBudget.termB
set_option pp.all true in
#print LiuWang.Proof.VaughanTypeIIBudget.termC
