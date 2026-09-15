# 第二弧与第三弧：原路线未付输入审查

## 结论与边界

- 快照：`main`；初始 HEAD `7e236a0008bf1ac1d4a7b923a8a4a34342f87315`，收尾 HEAD `f1476f0b217a3b10bf02e82af67d2dc5740841d3`。唯一主工作树 `/home/azureuser/liu-wang-ternary-goldbach-lean`。两目录的 HEAD 差异仅为父级新增 `LowHeight/ExpTangent.lean`，已复核正文。
- 严格保留 Liu–Wang 的 `N ≥ exp(3100)`、原弧域、权、端点与常数。本次仅源码只读审查并写本报告两文件：未改 Lean、未建分支/工作树、未编译、未启动证明/编码 CLI。源码存在及 `#print axioms` 指令不等于本次内核验证。
- **`.032281` 已闭，而且已接真实高段积分。** 当前 M1 合账仍有 `hseven`、原 `hnu` 和 `originalLowScalar`；第三弧 `.24981`、两个 `.00003`、`6e-9` 等数值也已闭，不重报标量缺口。
- **两项重要去重：** `htwo` 可由已证全家族 T2 加严格窗→较高闭窗桥支付；M6 的 `sourceNu q ≤ sourceNu(L⁶)` 可由同树 `nu_monotoneOn` 支付。二者是接线，不是未证解析定理。
- **低段必须分口径：** 旧 `actual_513_payment` 已证明同一实际低段 `.0000076` 上界；最新严格原积分 `originalLowScalar` 的固定证书与全实参数域估计仍未付。不能由实际计数的较小上界反推某个较大原积分的上界。
- 本树未附原论文扫描与旧私有源核报告；两个受审目录没有字面的 `SOURCE_CHECK` 标记。下文 `SOURCE_CHECK` 是本审查对**原域/截断对应**待核的分类，不是声称读到了旧私有核查结论。仓库 `docs/STATUS.md:20` 所说 (2.29)/(2.37) 属父级基础/HighSum，不冒充本次两个弧的新印式问题。

记 `L=log N`、`P=L³`、`P1=L⁶`、`T=L¹⁵`。第二弧取 `1≤q≤P`，`omega=3.36P/q`，`U=10πL⁷/q`，密度门 `D=max(100000/q,10000 log q)`。第三弧取 `P≤q≤P1`（实际 M3 见证严格 `P<q`），低高度 `10000π`，中高度仍为 `U`。所有 count 均保留 ordinary-L 的解析重数。

## 最新实际消费者

| 分量 | 当前实际出口 | 准确边界 |
|---|---|---|
| 第二弧 M1 | `OriginalV1.LowHeight.actual_M1_le_original_low_scalar` | `(8√q/φ(q))actualM1 ≤ (.032281 + 8 originalLowScalar(L))/L`；仍需 T7、原 totient-nu。 |
| 第二弧稀疏带/端点 | `OriginalV1.actual_two_strips_log_bound`、`truncated_endpoint_bound` | (5.16) 已付；(5.17) 原数值、整端点原数值及 c1 右尾仍须处理。 |
| 第三弧 sigma4 | `OriginalV1.Source521523.equation_5_27_original_conditional` | `.36938N/L` 已条件合账；仅剩原 totient、T7 低窗与 `LocalC1Data`。 |
| 第三弧 sigma5 | `Restart.equation_5_31_actual_count` | `.0011N/L` 已付；中高度端点及内积分仍显式保留。 |
| 第三弧 sigma6 | `OriginalV1.sigma6_original_reduction_with_real_tail` | `.00012+7/10³¹` 普通/端点价之外，仍有 `sourceM5`、已能支付的 `m6OriginalScalar`、`sourceHighRealTail`。 |

下列条目同时含数学输入、定量支付、源核和接线；**不应把总行数当作独立未证 lemma 数**。同一 T7/nu/c1 的不同消费者共享上游。

## 待办与 SOURCE_CHECK

### MINOR-T7 — `mathematical_input`

共享 Theorem 7 高 alpha 的实际全角色、解析重数密度输入仍未支付。第二弧 hseven、第三弧低窗 hdensity 与高端点 hhigh 是同一生产者的不同特化，不是三条独立密度定理。

- 源码：`LiuWang/Proof/SourceRoute/SecondArc/Continuation/ArithmeticPayment/CountPayment/Restart/OriginalV1/LowHeight/Assembly.lean:64`
- 具体消费者：`LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.LowHeight.actual_M1_le_original_low_scalar`
- 第二弧 N≥exp3100、1≤q≤L³：∀y≥densityGate(q)=max(100000/q,10000 log q)，∀alpha∈[1/2,1)，familyCount(q,alpha,y)≤sourceSevenBound(q,alpha,y)。
- 第三弧 L³≤q≤L⁶：低窗 y=10000 log q，alpha∈[59/60,1−0.478/log(q·10000π)]；高端点 y=T=L¹⁵、alpha=59/60。sourceDensity(q,y,alpha) 与 sourceSevenBound(q,alpha,y) 字面同式。低窗实际消费于 LiuWang/Proof/SourceRoute/ThirdArc/Continuation/ScalarPayment/Restart/OriginalV1/Source521523/Assembly.lean:43，高端点于 LiuWang/Proof/SourceRoute/ThirdArc/Continuation/ScalarPayment/Restart/OriginalV1/RealTail.lean:119。
- 同树 LiuWang/Proof/SourceRoute/Density/Restart/OriginalV1/FamilyAssembly.lean:107 的 family_sourceSeven_from_original_inputs 仍需 hprincipal、hchen：高 alpha 主角色 principalSevenBound 与 3≤q 时∀beta∈[1/2,1) 的严格非主 Chen 计数。已证低 alpha 和普通主角色 sourceSevenBound 不够代付整个家族。深层密度输入由父级审查共享。

### MINOR-NU-TOTIENT — `mathematical_input`

原 sourceNu 算术界未找到同树可直接实例化的无条件生产者；不同于 sourceNu 自身单调性/数值上界，也不同于已证多项式 totient 界。

- 源码：`LiuWang/Proof/SourceRoute/SecondArc/Continuation/ArithmeticPayment/CountPayment/Restart/OriginalV1/LowHeight/Assembly.lean:64`
- 具体消费者：`LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.LowHeight.actual_M1_le_original_low_scalar`
- 第二弧：N≥exp3100，1≤q≤L³，q/φ(q)≤sourceNu(L³)；小 q 须保留实际域，不得盲写 sourceNu(q)。
- 第三弧：L³≤q≤L⁶，q/φ(q)≤sourceNu(q)，供 Source521523/Assembly.lean:42、Source524/Consumer.lean:117、Source525526/Consumer.lean:34,48、M6Certificate/Payment.lean:73。
- sourceNu(x)=exp(γ)log log x+2.50637/(log log x)。对同树全部 Lean 源码检索 sourceNu、2.50637 及同式 nu 定义后，已见单调性与条件消费者，未定位该实际 totient 数值上界。

### M2-ORIGINAL-LOW-SCALAR — `quantitative_input`

严格原积分 originalLowScalar 的固定 3100 证书及所有实 L≥3100 上界尚未闭。旧 coupledKernel 已付同一实际低段，但其较强实际上界不推出原积分上界。

- 源码：`LiuWang/Proof/SourceRoute/SecondArc/Continuation/ArithmeticPayment/CountPayment/Restart/OriginalV1/LowHeight/Assembly.lean:64`
- 具体消费者：`LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.LowHeight.actual_M1_le_original_low_scalar`
- 所需原账：∀L∈ℝ，3100≤L → originalLowScalar(L)≤0.0000076；固定点认证与统一参数比较是同一工作包的两个验收项。
- 定义 LiuWang/Proof/SourceRoute/SecondArc/Continuation/ArithmeticPayment/CountPayment/Restart/OriginalV1/LowHeight/OriginalScalar.lean:18：区间 [3.36 L³,10000 L³ log(L³)]，被积函数 L·lowWeight(L³,y)·exp(−0.478(L+log0.001)/log y)。
- 现有 M1 合账是 (8√q/φ(q))actualM1≤(0.032281+8 originalLowScalar(L))/L。LowHeight/LogScalar.lean:45 只给精确换元；同树实际 lowHeightIntegral 的 .0000076 见 closed_examples，不再报成实际计数缺口。

### M2-T2-ADAPTER — `wiring`

htwo 是已证数学输入尚未接入，不是缺失的二零定理。

- 源码：`LiuWang/Proof/SourceRoute/SecondArc/Continuation/ArithmeticPayment/CountPayment/Restart/OriginalV1/SparseBands.lean:81`
- 具体消费者：`LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.actual_last_strip_log_bound`
- ∀x≥8e9，q≤x，∀alpha，1−0.2067/log x<alpha<1 → familyCount(q,alpha,x/q)≤2。
- 生产者 LiuWang/Proof/MultiZeroRepulsion/Continuation/GeneralFamily.lean:62 的 general_theorem_two；桥 LiuWang/Proof/SourceRoute/ThirdArc/Continuation/ScalarPayment/Restart/OriginalV1/Source525526/Count.lean:50 的 strict_to_closed_count。只需严格间隙与 Nat→Real cast。

### M2-LAST-STRIP-SCALAR — `quantitative_input`

(5.17) 已到实际计数的精确对数积分，但未发现这一原积分的终端数值支付；(5.16) 不同衰减率的证书不能代付。

- 源码：`LiuWang/Proof/SourceRoute/SecondArc/Continuation/ArithmeticPayment/CountPayment/Restart/OriginalV1/SparseBands.lean:81`
- 具体消费者：`LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.actual_last_strip_log_bound`
- N≥exp3100，1≤q≤L³；外系数 16N·q/φ(q)。区间 [log(3.36L³),log(10πL⁷)]。
- 核 exp(−z/2)[exp(−(L+log0.001)/(9.645908801 z))−exp(−0.2067(L+log0.001)/z)]。保持两项符号。
- T2 见 M2-T2-ADAPTER；原 nu 见 MINOR-NU-TOTIENT。公开树无原扫描，最终原十进制预算未核，不猜写。

### M2-ENDPOINT-SCALAR — `quantitative_input`

原截断端点停在 endpointDensityBound 与 14000 的显式右端，尚无此整式的原预算终端。已有 .0004 只支付旧消费者的端点尾，不能覆盖整段 59/60..siegelCutoff。

- 源码：`LiuWang/Proof/SourceRoute/SecondArc/Continuation/ArithmeticPayment/CountPayment/Restart/OriginalV1/Endpoint.lean:61`
- 具体消费者：`LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.truncated_endpoint_bound`
- N≥exp3100，1≤q≤L³，U=10πL⁷/q，hseven 见 MINOR-T7。
- 右端 U^(−1/2)[endpointDensityBound(q,U)exp(−0.478(L+log0.001)/log(10πL⁷))+14000 exp(−0.10367089(L+log0.001)/log(10πL⁷))]，加实际包外系数后支付。
- 同目录 Assembly.lean:119 的 endpointDensityBound_source_form 只是原参数展开，不是数值预算。

### M2-C1-TAIL-SOURCE — `SOURCE_CHECK`

从实际 full count 截到 siegelCutoff 的源域义务未接入：middlePacket 仍积分到 1，原截断端点/稀疏带只到 c1 界，不得静默删余尾。

- 源码：`LiuWang/Proof/SourceRoute/SecondArc/Continuation/ArithmeticPayment/CountPayment/Restart/Packet.lean:61`
- 具体消费者：`LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.middlePacket_low_alpha_and_endpoint_tail_paid_all_heights`
- 同一 N,q，y∈[omegaCutoff,U]；旧实际余带 stripUpper(q,y)..1，原截断出口 stripUpper(q,y)..siegelCutoff(q,y)。
- 需在实际零点载体上处理例外实零并付非实 c1 原窗排除。累计 familyCount 含 |Im rho|=0，而正下端 band 本身不含实零。
- 这是原域/截断对应待核，不能据此宣称原论文结论错误；和父级例外零/基础生产者共享。

### M2-ORIGINAL-ASSEMBLY — `wiring`

第二弧 .032281 与原低标量最新消费者尚未接成完整原域包/弧终端。较早强常数 10/5 的 packet 不是已接好的原 16/8 总账。

- 源码：`LiuWang/Proof/SourceRoute/SecondArc/OriginalIntegrals.lean:30`
- 具体消费者：`LiuWang.Proof.SourceRoute.SecondArc.source_57_middle_packet`
- 接实际 M1、端点、两稀疏带与 c1 尾，保持同一 N,q,a,eta 与解析重数。
- 局部已证 10 可放宽为原 16，但不授权改原路线、另降常数或重新分配预算。未付数学按本表共享依赖去重；根定理和其他弧归父级。

### M3-LOCAL-C1 — `mathematical_input`

第三弧 (5.21)–(5.27) 最新原消费者仍需存在 e 与 LocalC1Data q e；结构定义不是局部 LWD Lemma 2.1 的无条件实例。

- 源码：`LiuWang/Proof/SourceRoute/ThirdArc/Continuation/ScalarPayment/Restart/OriginalV1/Source521523/LocalSplit.lean:34`
- 具体消费者：`LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source521523.LocalC1Data`
- 原高度 lowHeight=10000π、尺度 x=q·lowHeight，L³≤q≤L⁶。e=some z 时需成员、lastUpper 右侧、实零、simple、非主、实角色、原始来源零点、987≤conductor≤x。
- 全家族 region：chi.LFunction rho=0，0<Re rho<1，|Im rho|≤lowHeight，lastUpper(q)<Re rho ⇒ e=some(chi,rho)。
- 实际消费 LiuWang/Proof/SourceRoute/ThirdArc/Continuation/ScalarPayment/Restart/OriginalV1/Source521523/Assembly.lean:47 的 hloc。已查同树实角色唯一性与部分小导子排除，但这些不自动给全角色非实零排除及此结构全部字段。

### M3-MIDDLE-ENDPOINT — `quantitative_input`

sigma5 的实际中高度端点尚未支付。已闭 (5.41) 的 T=L¹⁵ 高端点预算不能代替 U=10πL⁷/q。

- 源码：`LiuWang/Proof/SourceRoute/ThirdArc/Continuation/ScalarPayment/Restart/OrdinaryPayment.lean:82`
- 具体消费者：`LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.equation_5_31_actual_count`
- N≥exp3100，L³≤q≤L⁶，X=0.001N，未付项 (16N√q/(φ(q)√U)) countIntegral(q,X,U,59/60,1)。
- 已有 SourceWindows.lean:60、TablePayments.lean:109 的实际密度余项/表价拆分；密度门问题见 M3-DENSITY-DOMAIN-SOURCE。

### M3-MIDDLE-HEIGHT — `quantitative_input`

sigma5 的实际中高度内积分未到原数值终端；Fubini、移动 strip 与表价变换已闭，不重做。

- 源码：`LiuWang/Proof/SourceRoute/ThirdArc/Continuation/ScalarPayment/Restart/OrdinaryPayment.lean:82`
- 具体消费者：`LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.equation_5_31_actual_count`
- 未付 (8N√q/φ(q))∫[10000π,U] y^(−3/2)countIntegral(q,0.001N,y,59/60,1)dy。
- 需付 59/60..(1−0.478/log(qy)) 实际密度部分、近一表价部分以及原 c1/实零边界。完整原域 N≥exp3100、L³≤q≤L⁶，不能只取满足密度门的子区间。
- 已证 HeightPayments.lean:92,114,143 的表拆分/对数换元右侧仍有积分。

### M3-DENSITY-DOMAIN-SOURCE — `SOURCE_CHECK`

第三弧原中高度及高窗下端不统一达到 Theorem 7 高度门；仓库已证明原整数域 U<10000 log q 的见证。不能把 T7 直接用于整个 [10000π,U] 或 [U,T]。

- 源码：`LiuWang/Proof/SourceRoute/ThirdArc/Continuation/ScalarPayment/Restart/OriginalV1/DensityDomainCheck.lean:40`
- 具体消费者：`LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.original_integer_density_domain_failure`
- 见证 N=ceil(exp3100)、q=3100⁶，满足 N≥exp3100、L³<q≤L⁶，但 middleHeight(N,q)<10000 log q。
- 影响 OrdinaryPayment.equation_5_31_actual_count 与 RealTail.sigma6_original_reduction_with_real_tail 的 sourceM5。须回原论文核合法分段、原普通计数支付或原高度替换；不得缩 q 域、改 N 门槛或称贡献为零。
- 仅否定直接域包含，不否定原总预算；本公开树未含原扫描，源文细节仍待核。

### M3-HIGH-M5 — `quantitative_input`

sigma6 的高高度 bulk sourceM5 仍在右侧；它不是已闭 sourceM6 标量。

- 源码：`LiuWang/Proof/SourceRoute/ThirdArc/Continuation/ScalarPayment/Restart/OriginalV1/RealTail.lean:116`
- 具体消费者：`LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.sigma6_original_reduction_with_real_tail`
- sourceM5=(5N√q/φ(q))∫[U,T]y^(−2)countIntegral(q,N,y,59/60,1−0.478/log(qy))dy。
- N≥exp3100、L³≤q≤L⁶；密度母输入见 MINOR-T7，低于 gate 部分见 M3-DENSITY-DOMAIN-SOURCE。保持同 q、原权和端点后付原预算，不能以 M6 的 6e−9 抵消未知 bulk。

### M3-HIGH-LOCAL-REGION — `mathematical_input`

高高度 hlocal 尚未由完整原 c1 非实零排除实例化；实角色唯一性与若干低虚部支不覆盖全角色移动窗。

- 源码：`LiuWang/Proof/SourceRoute/ThirdArc/Continuation/ScalarPayment/Restart/OriginalV1/RealTail.lean:116`
- 具体消费者：`LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.sigma6_original_reduction_with_real_tail`
- ∀y∈[U,T]，∀chi,rho，chi.LFunction rho=0，0<Re rho<1，|Im rho|≤y，1−1/(9.645908801 log(qy))<Re rho ⇒ Im rho=0。
- 它仅识别余累计计数为实零计数，不推出余项=0；与 M3-LOCAL-C1 共享局部原零区域基础，不重复另开零区域理论。

### M3-HIGH-REAL-TAIL-SOURCE — `SOURCE_CHECK`

sigma6 原正下端 band 不含实零，但累计 familyCount 的 Abel 上界引入 sourceHighRealTail；不能凭 hlocal 删除。

- 源码：`LiuWang/Proof/SourceRoute/ThirdArc/Continuation/ScalarPayment/Restart/OriginalV1/RealTail.lean:79`
- 具体消费者：`LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.sourceHighRealTail`
- 原保留项 (5N√q/φ(q))∫[U,T]y^(−2)countIntegral(q,N,0,1−0.10367089/log(qy),1)dy。
- RealTail.lean:84 精确分解、:116 sigma6 消费者都显式保留。需按原非实 band 的忠实计数 Abel 回接，或使用原文允许的例外零支付。
- 低 sigma4 的 primedSigma4 分解不自动消除移动高窗累计实尾；累计尾非零可能性也不说明真实高 band 有实零。

### M3-NU-MONOTONE-ADAPTER — `wiring`

M6 的 hnu 是同树现成同式单调性未接，不是独立数学或数值缺口。

- 源码：`LiuWang/Proof/SourceRoute/ThirdArc/Continuation/ScalarPayment/Restart/OriginalV1/M6Certificate/Payment.lean:70`
- 具体消费者：`LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.M6Certificate.equation_5_44_paid`
- 需 sourceNu(q)≤sourceNu(L⁶)，原域 q≥L³≥100000、q≤L⁶。
- MajorOrdinary/Continuation/Nu.lean:59 的 nu_monotoneOn 覆盖 [100000,∞)，两个定义同式；也可用 Source524/FirstMonotone.lean:14 的 logNu_monotone（log q≥24）。
- 仍需 MINOR-NU-TOTIENT 的 q/φ(q) 估计；单调性不支付该算术不等式。

### M3-ORIGINAL-ASSEMBLY — `wiring`

第三弧最新 sigma4=.36938 与 M6=6e−9 尚未接至同一 S/primeS 原域总账；旧 S_four_new_payments 仍留整段实际余项。

- 源码：`LiuWang/Proof/SourceRoute/ThirdArc/Continuation/ScalarPayment/Restart/OrdinaryPayment.lean:110`
- 具体消费者：`LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.S_four_new_payments`
- 保持 sourceIndex(a,q)、L³<q≤L⁶、|eta|≤L⁷/(qN)、N≥exp3100 与同一有理弧见证。
- 以 Source521523.equation_5_27_original_conditional 代换整个 sigma4，不再把 .11585 叠加到旧 exceptionalTailBill 上。
- M6 已闭数值，应接 M6Certificate.equation_5_44_paid；其余未付依本表去重。根圆法总装及第四弧由父级负责。

## 同树已闭生产者：禁止重报

- **C-M2-032281**：原 originalDensityScalar(L)≤32281/1000000 对所有实 L≥3100 已证明；固定点 original_fixed_032281 与 recovery_rational_budget 生产链俱在，不再报 .032281 数值缺口。
  - `LiuWang/Proof/SourceRoute/SecondArc/Continuation/ArithmeticPayment/CountPayment/Restart/OriginalV1/Fixed032281/RecoveryBudget.lean:57`
  - `LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.original_all_L_032281`
- **C-M2-032281-ACTUAL**：已把 .032281 接至 max(omegaCutoff,densityGate)..middleUpper 的真实 familyCount 积分，仅保留 hseven/hnu；不是孤立标量。
  - `LiuWang/Proof/SourceRoute/SecondArc/Continuation/ArithmeticPayment/CountPayment/Restart/OriginalV1/Fixed032281/RecoveryActual.lean:30`
  - `LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.actual_high_branch_032281`
- **C-M2-LOW-COUNT**：主/非主 ordinary-L 原低高度 source24 计数已付；其运输到原低积分已在 LowHeight/ActualHeight.lean:48 证明。
  - `LiuWang/Proof/SourceRoute/SecondArc/Continuation/ArithmeticPayment/CountPayment/Restart/OriginalV1/LowHeight/ActualCount.lean:30`
  - `LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.LowHeight.familyCount_le_source24`
- **C-M2-513-ACTUAL**：同一实际 lowHeightIntegral 的 .0000076 已闭（actual_513_normalized_sharp 更强 .000006510372/L）；走 coupledKernel，不能推 originalLowScalar≤.0000076。
  - `LiuWang/Proof/SourceRoute/SecondArc/Continuation/ArithmeticPayment/CountPayment/Payment.lean:69`
  - `LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.actual_513_payment`
- **C-M2-516-SCALAR**：原 (5.16) 标量 112000 L sourceNu(L³) 乘原积分≤.000021 已闭。
  - `LiuWang/Proof/SourceRoute/SecondArc/Continuation/GaussianPayment.lean:154`
  - `LiuWang.Proof.SourceRoute.SecondArc.Continuation.original_516_scalar_payment`
- **C-M2-516-ACTUAL**：实际 full-family strip 的 .000021N/L 已无 hphi（更强 .00001777664）；旧 OriginalPayment 的 hphi 不应导致重报整个 (5.16)。
  - `LiuWang/Proof/SourceRoute/SecondArc/Continuation/ArithmeticPayment/Payment.lean:56`
  - `LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.actual_516_payment`
- **C-M2-LOW-ALPHA**：实际低 alpha 外权 10N√q/φ(q) 的 .00065N/L 已付；原 .000065/L 标量亦已付。
  - `LiuWang/Proof/SourceRoute/SecondArc/Continuation/ArithmeticPayment/CountPayment/Restart/LowAlpha.lean:85`
  - `LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.actual_low_alpha_strong_payment`
- **C-T2**：x≥8e9、q≤x 的全家族计重严格窗≤2 已无额外数学假设；第三弧已调用，第二弧 htwo 仅待接。
  - `LiuWang/Proof/MultiZeroRepulsion/Continuation/GeneralFamily.lean:62`
  - `LiuWang.Proof.MultiZeroRepulsion.Continuation.general_theorem_two`
- **C-NU-MONO**：同一 exp(γ)loglog+2.50637/loglog 函数在 [100000,∞) 已证单调；这不是 q/φ(q) 的生产者。
  - `LiuWang/Proof/SourceRoute/MajorOrdinary/Continuation/Nu.lean:59`
  - `LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.nu_monotoneOn`
- **C-M3-523**：原 (5.23) 实际 lowBetaBill≤.00365N/L，N≥exp3100、q≤L⁶，无 hdensity/htotient。
  - `LiuWang/Proof/SourceRoute/ThirdArc/Continuation/ScalarPayment/Restart/OriginalV1/Source521523/BaseConsumer.lean:64`
  - `LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source521523.equation_5_23_original`
- **C-M3-524-SCALAR**：原 (5.24) originalBracket 在全部 L≥3100、3≤x≤6 的 .24981 数值预算已闭；实际原消费者保留 htotient、hdensity。
  - `LiuWang/Proof/SourceRoute/ThirdArc/Continuation/ScalarPayment/Restart/OriginalV1/Source524/Payment.lean:95`
  - `LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524.originalBracket_paid`
- **C-M3-525526-SCALAR**：scalar525 与 scalar526 在 L≥3100、3≤x≤6 各≤3/100000 已闭；Source525526/Count 已接 T2，实际原支付仅保留 htotient。
  - `LiuWang/Proof/SourceRoute/ThirdArc/Continuation/ScalarPayment/Restart/OriginalV1/Source525526/Scalar.lean:181`
  - `LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source525526.scalar525_paid`
- **C-M3-521-SCALE**：单个原低零项 .11585 标量已付；不包含 LocalC1Data 的存在与全角色唯一性。
  - `LiuWang/Proof/SourceRoute/ThirdArc/Continuation/ScalarPayment/Restart/OriginalV1/Source521523/SingleScale.lean:93`
  - `LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source521523.equation_5_21_original`
- **C-M3-527-CONDITIONAL**：实际 sigma4≤.36938N/L 条件合账已证；准确保留 htotient、hdensity、hloc，不是又缺 .36938 标量。
  - `LiuWang/Proof/SourceRoute/ThirdArc/Continuation/ScalarPayment/Restart/OriginalV1/Source521523/Assembly.lean:39`
  - `LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source521523.equation_5_27_original_conditional`
- **C-M3-530540**：sigma5 的 .0011N/L 与 sigma6 的 .00012N/L 普通计数部分均已到实际零和；高 alpha 项显式保留。
  - `LiuWang/Proof/SourceRoute/ThirdArc/Continuation/ScalarPayment/Restart/OrdinaryPayment.lean:40`
  - `LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.sigma5_low_beta_paid`
- **C-M3-541-SCALAR**：T=L¹⁵ 高端点标量 7/10³¹ 已闭，equation_5_41_actual_count 仅留真实密度；不重报高端点标量。
  - `LiuWang/Proof/SourceRoute/ThirdArc/Continuation/ScalarPayment/Restart/HighEndpoint.lean:42`
  - `LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.equation_5_41_explicit`
- **C-M3-544-SCALAR**：所有实 L≥3100 的 m6OriginalScalar≤6/1000000000 已闭；equation_5_44_paid 已到 sourceM6，仅留 htotient/hnu。
  - `LiuWang/Proof/SourceRoute/ThirdArc/Continuation/ScalarPayment/Restart/OriginalV1/M6Certificate/Payment.lean:66`
  - `LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.M6Certificate.m6OriginalScalar_le`
- **C-M3-PRINCIPAL**：主角色及展开误差已付 .000000680001N/L；ErrorBudget.primePower_error_paid 另付素数幂误差，不重开该账。
  - `LiuWang/Proof/SourceRoute/ThirdArc/Continuation/Principal.lean:49`
  - `LiuWang.Proof.SourceRoute.ThirdArc.Continuation.S_principal_and_error_paid`
- **C-T7-LOW**：原高度门上的 alpha≤1/2+2sourceDelta(y) 已闭；另有 y≥10000、alpha≤2/3 生产者，但不覆盖本次高 alpha 实际消费域。
  - `LiuWang/Proof/DirichletZeroCount/Applications/LowAlpha.lean:89`
  - `LiuWang.Proof.DirichletZeroCount.Applications.familyCount_le_sourceSeven_original_low`

- **C-M2-LOW-TANGENT**：父级同树新增 `original_low_exp_le_tangent`，证明所有 `L≥3100`、`c∈ℝ`、`z>0`、`b>0` 的原指数切线上界；保留原参数 `0.478*(L+log .001)`，无额外数值假设。
  - `LiuWang/Proof/SourceRoute/SecondArc/Continuation/ArithmeticPayment/CountPayment/Restart/OriginalV1/LowHeight/ExpTangent.lean:53`
  - 未接入 `originalLowScalar` 积分消费者，不是 `7.6e−6` 固定预算或全参数积分上界；**M2-ORIGINAL-LOW-SCALAR 保持不变**。父级报告该新增文件严格编译、官方 checker 与五项标准公理检查通过，本次未独立重跑。

## 原域 SOURCE_CHECK 的最小验收规则

1. **T7 高度门不能省。** 第二弧已经按 `max(omega,D)` 分高段，原低段另付；第三弧的 `DensityDomainCheck.original_integer_density_domain_failure` 则证明直接域包含失败。它不证明论文整体错误，也不证明真实积分有超额。
2. **累计 count 不等于正下端 band。** 实零不属于原中/高 band，却可出现在积分中的累计 familyCount。`hlocal` 只把 c1 右尾识别为实零尾，不付该尾；`LocalC1Data` 只给低 sigma4 的局部选零语义，不自动给高窗消尾。
3. **原低积分与旧实际低界不能互换。** `coupledKernel` 与 `lowWeight` 不同，旧 `.000006510372` 实际归约不等于最新 `originalLowScalar` 的原固定积分证书。
4. **原常数放宽需显式合账。** 已证局部常数 10 不妨推出 16，但不得据此改写用户要求的原 16/8 分账、另造总体预算或降低目标门槛。

## 推荐一个最短可直接推进的原论文接点

优先接第二弧原 (5.17) 的 `htwo`：复用 `MultiZeroRepulsion.Continuation.general_theorem_two`，再用 `ThirdArc...Source525526.strict_to_closed_count`，按 `1−0.2067/log x < alpha` 保留严格间隙并做 Nat→Real cast。这样可消掉 `actual_last_strip_log_bound` / `actual_two_strips_log_bound` 的一个外部假设，**无需重做二零排斥或数值计算**。这里只建议，不写 Lean；这不等于 (5.17) 原标量已经付清。

若父级只接受“新增数学而非接线”，当前最小明确原对象是 `originalLowScalar(3100)≤7.6e−6` 的固定积分证书；它还须另有全 `L≥3100` 统一比较才能关闭原低标量工作包，不能以一次浮点结果替代。

## 覆盖与验证

- 声明/前提/引用索引覆盖 SecondArc `226` 个 Lean 文件、ThirdArc `74` 个 Lean 文件。JSON 附该集合各文件 SHA-256；这表示源码快照覆盖，不声称逐个恢复数值块重算。
- 已定位 `17` 条账本记录、`20` 个已闭例证；类型分布：`SOURCE_CHECK` 3，`mathematical_input` 4，`quantitative_input` 6，`wiring` 4。共享上游与工程接线不能加总成数学缺口数。
- 两文件由同一结构化记录生成，JSON schema、ID 唯一性、source 相对路径/行号及消费者声明名均已程序检查。未启动 Lean 验证。
- 父级负责根闭合、基础深层来源与第四弧；本报告只列它们在第二/第三弧的实际依赖接口，不扩展研究范围。
