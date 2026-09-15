# 连续检查点与恢复约定

用户授权：本项目每个具体缺口通过父级验收、接入实际消费者后，立即创建并推送检查点，不等待其它并行任务。只发布显式允许清单内的源码、状态及验证摘要；CLI正常退出不触发自动接纳。

## 当前检查点

主入口：`LiuWang.Proof.Campaign20260915.Accepted`。
主结论出口：`LiuWang.Proof.Campaign20260915.Parent.DensityPaidRoot.threeOddPrimes_of_three_shared_inputs`。

原大数范围的完整零密度输入M01已消去，尚有M04（原有限高度ζ验证）、M06（全域totient）、M07（小导子排除）。此为显式定理参数，不是新增数学公理。阈值以下衔接单独未闭。

本次同时纳入已父验的Mordell–Phi定向积分与真实源核运输、固定Hankel临界带表示、Littlewood恒等式、实际零点计重/对数积分，以及totient中段和有效解析/去平滑构件。范围与未付输入见各源码定理签名；不将这些构件冒充完整数值验证或全域totient。

## 本次追加：完整有限极点穿越

`Parent.AnnularHankelAudit.actual_zeta_after_pole_crossing` 已核收：实际 ζ 穿越完整整数极点族后，得到两个有限和与精确前因子，余项仍是扩大的圆弧 Hankel。C2 实际无限积分及连接边极限已证，但中央有限路径同一性与有效余项未闭，不冒充最终 Riemann–Siegel 公式。原主线仍有 M04/M06/M07。

## 本次追加：完整高阶谱与去平滑组件

`Parent.TotientFullSmoothingAudit.actual_psi_moment_bounds` 已实际消费完整m阶谱、积分常数消去、Γ/平凡零点修正及双向去平滑。对实际素数幂加权计数函数ψ得到两侧零点矩表达式；根式δ/ε终端明确保留低零点验证、逆幂矩k、真实高窗预算B及数值条件。未宣布原完整Theorem28或全域totient完成，整数覆盖仍为log q≤1340。

## 本次追加：真实多项式补集尾预算

`Parent.PolynomialExteriorAudit.actual_polynomial_exterior` 已核收实际七项Taylor多项式补集的绝对积分预算。外段估计独立于参数到整数的距离，包含整数参数；局部Hankel消费者仍保留中央Jn和全轮廓整数极限的未付部分。未宣布完整R0/R2或M04闭合。

## 本次追加：冻结跨任务接口

`Parent.CrossLaneHandoff` 核收Gram点相位/计数接口及实际ξ/ζ带重数加权运输。两个基础模块进入发布闭包后冻结；未核的上游草稿不能仅因可见就被其它任务导入。构建入口增加父级交接准入检查；该措施不改变Lean逻辑检查，也不把通用接口算成数值验证或主根闭合。

## 本次追加：原C2右无限尾的有效预算

M04-V03已核收。`Parent.RightC2TailAudit.actual_prefactored_right_tail` 控制真实右无限支并包含原Hankel前因子，保持原exp(-t/11)衰减，不使用局部Taylor半径覆盖无穷尾。尾界含整数参数；完整C2的左支、中央Jn及最终总余项仍单列未闭。

## 本次追加：真实中央轮廓变形

M04-V01已核收。`Parent.CentralC2Audit.actual_zeta_C2` 直接使用已证明的中央有限路径等式及真实无穷极限，把实际ζ的余项接到原C2，而非附加同伦或积分相等假设。非整数窗口保持m<eta<m+1；整数参数延拓和完整误差仍独立未闭。

## 断联后的恢复原则

以本仓库主根、最新验证摘要和明确的任务分解文档恢复，不以聊天中的计划或CLI退出消息认定闭合。保留一个main主工作树；活跃工作者只写独占新模块，父级核收后冻结、构建并发布。未验草稿、运行日志、扫描文献、凭据和私有会话不在公开包内。

每次发布必须通过实际闭包编译/官方精确重放、源码与对象绑定、定理签名及公理检查、发布allowlist及暂存差异检查；push后读回远端main哈希。失败时保留本地证据，不声称远端已保存。
