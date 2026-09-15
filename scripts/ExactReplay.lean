import LeanChecker

/-!
精确调用当前工具链未修改的官方 `replayFromImports`。
原 CLI 把目标当命名空间前缀，并并发检查所有匹配模块；本驱动只修正选择方式。
这不是 --fresh，也不是另写的证明检查器；所有 module data parts 仍由官方函数读取。
模块名通过单个环境变量传入；缺失、空名和不存在的模块均必须返回错误。
-/

unsafe def ExactModuleReplay.run : IO Unit := do
  let some target ← IO.getEnv "LIUWANG_EXACT_REPLAY_MODULE"
    | throw <| IO.userError "LIUWANG_EXACT_REPLAY_MODULE is required"
  if target.isEmpty || target.startsWith "-" then
    throw <| IO.userError "expected a nonempty module name, not a flag"
  let name := target.toName
  if name.isAnonymous then
    throw <| IO.userError "anonymous module is forbidden"
  Lean.initSearchPath (← Lean.findSysroot)
  let object ← Lean.findOLean name
  IO.println s!"OFFICIAL_CORE_EXACT_BEGIN {name} {object}"
  replayFromImports name
  IO.println s!"OFFICIAL_CORE_EXACT_PASS {name}"

#eval ExactModuleReplay.run
