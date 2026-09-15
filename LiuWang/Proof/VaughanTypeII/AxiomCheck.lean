import LiuWang.Proof.VaughanTypeII.Consumer
import Lean.Util.CollectAxioms

/-! 全部本命名空间声明的完整类型与传递公理清单；非标准公理使编译失败。 -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let ns := `LiuWang.Proof.VaughanTypeII
  let declarations := env.constants.toList.filter fun (name, _) =>
    ns.isPrefixOf name || name.toString.startsWith "_private.LiuWang.Proof.VaughanTypeII."
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
    logInfo m!"TYPEII_AUDIT {row.compress}"
