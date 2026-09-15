# 并行任务中断的诊断与修复

## 已核实原因

systemd 用户日志将最初任务及后续恢复任务记为 `oom-kill`；内核日志明确 `CONSTRAINT_MEMCG`，被杀进程为 `leanchecker`。任务外层随后收到 SIGTERM。CLI 的 “Operation aborted by user” 文案不足以证明用户主动停止。

直接触发点为 `AnalyticNumberTheory` 聚合模块。当前 LeanChecker 官方源码第91–108行按命名空间前缀收集匹配模块，并对每个目标创建 `IO.asTask`。父级原先只在外层加全局编译锁，仍允许一个checker进程内部并发重放整个前缀族。这是父级启动/验证工程错误，不是数学证明失败。

## 修复与不变项

- `scripts/ExactReplay.lean` 直接调用当前工具链未修改的官方 `replayFromImports`，只选择一个精确模块；官方函数继续读取 exported/server/private module data parts。
- 新记录标 `official-core-exact-replayFromImports`。不是原CLI成功，也不是 `--fresh` 全导入环境重放。
- 保留原全局单模块编译锁、原任务内存限制、已核成功缓存和全部失败日志；不放宽内存、跳过检查或改动数学定义。
- 当前helper与官方core对象哈希、实际目标对象路径、check完成标记和日志哈希入新回执。旧成功记录不倒填成新模式证据。
- 增加按模块/源依赖键/命令模式/驱动版本绑定的执行标记：若相同执行没有终态，或以资源中断结束，后续请求直接返回阻塞，不再轮流杀死所有等待者。

## 实际验证

- 缺失模块变量、空模块名、不存在模块三项负控制均非零退出，且没有PASS标记。
- 已知证明叶及先前OOM的 `AnalyticNumberTheory` 都完成精确重放。
- 上述后台预检实际处于 `memory.max=4294967296` 的任务scope中成功；没有提升原4GiB限制。RSS不能代替cgroup峰值，本次不宣称测得该峰值。
- 统一gate对 `AnalyticNumberTheory` 的62模块闭包通过，复用已有前缀，仅重新完成此前未获成功终态的聚合模块。
- 执行标记的显式负控制返回75，未生成目标对象；独立正控制真实编译与精确重放通过。这些是基础设施测试，不是新的数论进展。

私有诊断与控制结果在 `.lake/campaign-20260915/oom-recovery/`。所有13路恢复继续原会话、原写域、单main主树；恢复后仍逐项验收数学交付，不把源文件/草稿存在等同定理闭合。
