# Density / Exception 当前消费者缺口审查

## 结论与边界

当前源码归并为 **6 个尚未提供的数学合同**及 **2 个 SOURCE_CHECK 来源验收包**。这是去重合同清单，不是逻辑独立的未证引理数，更不是全项目缺口总数。
最重要的修正：**主字符密度、非主字符 0.3918 Gamma 上界、Chen (11)/(12)、(3.36)、Lemma 3.4/3.5 的终点均不能再当成数学缺口**；同树已有生产者。原文中间的 Chen (24)、Lemma 14 仍须与“终点另已证明”分别记账。

主论文目标严格为 `∀ N : ℕ, Odd N → Real.exp 3100 ≤ (N : ℝ) → IsThreeOddPrimeSum N`（`LiuWang/Target.lean:20`）。允许三个奇素数重复；不是 `10^3100`，本报告也不把更小奇数的有限补全塞入这个目标。

只读基线：唯一工作树 `/home/azureuser/liu-wang-ternary-goldbach-lean`，`.git/HEAD` 指向 `refs/heads/main`，读取的提交为 `7e236a0008bf1ac1d4a7b923a8a4a34342f87315`。未运行编译、git 或其他外部 CLI，未修改 Lean；只写本 Markdown 与同名 JSON。报告证据是当前源码静态审查，不是当前快照的内核验收。

## 尚未提供的数学输入

### DE-DENS-CHEN — 数学输入未提供

Chen 非主字符原密度上界尚未提供：严格左边界、闭高度窗、全部非主字符及普通 L 函数解析重数。当前闭窗转换与 T7 合账只是消费者。整族乘积/Jensen 路线仍落在实际 familyMean、familyMaximum 或 diskEnergy，不是此数值上界；这些受阻下游不另计缺口。

- **源码锚点**：`LiuWang/Proof/SourceRoute/Density/Restart/OriginalV1/FamilyAssembly.lean:130`
- **具体消费者**：`LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.complete_family_sourceSeven_from_original_inputs; LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.closed_nonprincipal_of_chen`
- 同一 q≠0、y≥max(100000/q,10000 log q)；q≥3 时须 ∀β∈[1/2,1), strictNonprincipalCount(q,β,y)≤(250359/log(qy)+5700)(q³y⁴)^(1−β)log(qy)^(6β)。
- 原函数定义及边界：LiuWang/Proof/SourceRoute/Density/Restart/OriginalV1/ChenBoundary.lean:21；原式系数：同文件:59。不能只证明 primitive 字符子族，也不能用较窄 α 区间代替全部消费者区间。
- 同树低 α 全族密度已有生产者；非主高 α 定量输入未找到无条件生产者。主字符 hprincipal 另有同域更强生产者，见 closed_examples，不列缺口。

### DE-DENS-CHEN24 — 原文中间输入未提供（终点另已证）

Chen (24), k=1 的字面 mollifier 均方估计仍作为 hchen24 传入。此项是原证明过程的未付输入，不是声称 Lemma 3.4 或 Lemma 3.5 的结论无人证明。

- **源码锚点**：`LiuWang/Proof/SourceRoute/Density/Restart/OriginalV1/Critical336/Consumer.lean:54`
- **具体消费者**：`LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.Critical336.lemma_3_5_at_source_shift_with_zeta_paid; LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.Critical336.lemma_3_4_with_zeta_paid; LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanBudgets.equation_3_44`
- y≥10000 log 6；∀u≥0, ∫[-yu,yu] ‖Q(y,1/2+it)‖² dt ≤ y(2.19021u+2.906)log y；source-shift 消费者从其原高度条件推出该 y 域。
- Q 必须保留同一严格实 cutoff；常数、u 的无界量词不可改。
- 已有 Sharp.Q_mean_sieved / sieved_mean_budget 给出较粗的 Q 均方界，并足以直接证明相同 Lemma 3.4 终点，但不等于这里的 Chen (24) 合同。对应生产者：LiuWang/Proof/GlobalZeroDensity/Sharp/SievedMean.lean:86、:97、:116。

### DE-DENS-CHEN14 — 原文中间输入未提供（终点另已证）

Chen Lemma 14 的原右线均方输入 hchen14 未提供；加权积分、核矩、插值消费者已实现。既有直接加权右端估计和 Lemma 3.5 不可被标成重新证明了这一全 u 的原输入。

- **源码锚点**：`LiuWang/Proof/SourceRoute/Density/Restart/OriginalV1/Critical336/Consumer.lean:57`
- **具体消费者**：`LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.Critical336.lemma_3_5_at_source_shift_with_zeta_paid; LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanBudgets.equation_3_45; LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanBudgets.equation_3_46`
- y≥10000 log 6；δ(y)=1/(1.5 log y)；∀u≥0, M(y,1+δ(y),yu)≤(67.929+0.0003u)log(y)^5。
- LiuWang/Proof/GlobalZeroDensity/MeanInterpolation/RightMean.lean:115 给出另一条线性上界；WeightedRight.lean:114 已证所需加权右端 90.5727 log(y)^5，但不提供此字面未加权窗口输入。

### DE-EX-GAMMA-LOW — 数学输入未提供

主字符/ζ 的 McCurley 低高度 Gamma 差分严格估计未提供。δ=2 的 gammaTerm 不可用普通非主字符 δ=0/1 的 Gamma 估计替代；低高度全窗也不能由 t=0 一点代替。

- **源码锚点**：`LiuWang/Proof/SourceRoute/Exception/Restart/OriginalV1/PrincipalIdentity.lean:67`
- **具体消费者**：`LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1.l24_low_of_gamma_estimate`
- 1<σ<1.15；∀|u|<1, gammaTerm(2,σ,u)<0.0615。
- gammaTerm 定义：LiuWang/Proof/SourceRoute/Exception/Restart/OriginalV1/ZeroTransport.lean:83；保留 K=1/√5 及 Stechkin σ₁。
- 同树 Sharp.shiftedGamma_real_bound 只覆盖 t=0；Sharp.shiftedGamma_all_height 的一般费用尚不足以支付原严格低估计。LiuWang/Proof/ZeroRegionFamily/Sharp/Principal.lean:82、:100。LowSum 的 hgammaLow 是同一输入的另一种写法，不另计。

### DE-EX-GAMMA-HIGH — 数学输入未提供

主字符/ζ 的 McCurley 高高度 Gamma 差分严格估计未提供。principalEulerDifference、有号完整零点和与极点项的处理均已提供，但这些恒等式不支付 0.3316。

- **源码锚点**：`LiuWang/Proof/SourceRoute/Exception/Restart/OriginalV1/PrincipalIdentity.lean:80`
- **具体消费者**：`LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1.l24_high_of_gamma_estimate`
- 1<σ<1.15，1≤|t|；gammaTerm(2,σ,t)<κ log|t|+0.3316，κ=(5−√5)/10。
- 已有 Sharp.shiftedGamma_all_height 保留较大费用 23/40−11K/30，不能当作此严格常数。LowSum 的 gammaHalfDifference、高估计 hgammaHigh 与本项同一对象（展开后），应合并。

### DE-EX-ORIGINAL-REGION — 原域覆盖输入未提供（跨模块共享）

原 c1=9.645908801 区域的无预给实种子分类/非实零排除仍未由当前 Exception 消费者提供。固定真实二次例外源后，跨字符、跨模数唯一性和单重性已经证明；未付的是从任意原窗口零点出发的完整原域输入，尤其无例外分支及移动高度的非实尾部，绝不是必须无条件存在一个例外零。

- **源码锚点**：`LiuWang/Proof/SourceRoute/ThirdArc/Continuation/ScalarPayment/Restart/OriginalV1/RealTail.lean:87`
- **具体消费者**：`LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.equation_5_42_with_real_tail; LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.original_low_sum_of_short_absence; LiuWang.Proof.SourceRoute.Exception.Restart.paper_source_original_zero_iff（仅提供已有实源分支）`
- 移动高度实际消费 hlocal：∀y∈[middleHeight(N,q),sourceT(N)], ∀χ,ρ，Lχ(ρ)=0、0<Reρ<1、|Imρ|≤y、1−1/(c1 log(qy))<Reρ ⇒ Imρ=0。不能从给定 datumL(d,β)=0 的 fixed_source_characterization 得出它。
- 低模数消费者还需 hshort（短原窗无零的分支条件）及 hcomplex：paperCap≤Reρ 且 Imρ≠0 时 Reρ≤cap(N,1/c1)。hshort 本身可作为无例外分支条件，不把它当成需全局成立的定理；关键是原域分类及高窗非实零估计。见 LiuWang/Proof/SourceRoute/LowSum/Continuation/Restart/NoExceptionAssembly.lean:109。
- 原 R24/R20 生产者、固定实源 Restart.Family、低高度三次/二次特殊分支各有真证明，但不足以替换完整原区域。原严格/闭边界须分别处理；不要求把严格源区域擅自加强为闭区域无条件无零。

## 原文 SOURCE_CHECK（不宣称已核）

本节 SOURCE_CHECK 是报告分类；不能理解为各 Lean 文件都有同名字面标签。当前树明文 `SOURCE_CHECK` 只见于 README/STATUS；STATUS 指名的 (2.29)、(2.37) 在本次目录范围外，继续待核且不重复计入数学输入。树内未含论文 PDF/TeX，本次未逐页检查原文，不能报告“原文全验证”。

### DE-SOURCE-CHECK-DENSITY

SOURCE_CHECK：Chen 原密度定理的完整假设尚未从当前树所含原文证据核定；同时需核 Chen (24), k=1 与 Lemma 14 到 LWD 原证明链的准确归属、常数、截断及量词。该项是来源验收，不是重复计算前述数学不等式。

- **源码锚点**：`LiuWang/Proof/SourceRoute/Density/Restart/OriginalV1/ChenBoundary.lean:5`
- **消费者**：`LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.closed_nonprincipal_of_chen; LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.complete_family_sourceSeven_from_original_inputs; LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.Critical336.lemma_3_5_at_source_shift_with_zeta_paid`
- 源码明确写 Chinese original p.687，且 supplied transcription does not settle every hypothesis。LWD p.285 Lemma 3.4 及 Chen (24) 的归属见 LiuWang/Proof/SourceRoute/Density/Restart/OriginalV1/CriticalMean.lean:7；LWD p.288 合账见 LiuWang/Proof/SourceRoute/Density/Restart/OriginalV1/FamilyAssembly.lean:5。
- 当前主树未含 PDF/TeX 原文；本次仅检视源码注释及定理类型，未逐页检查文献。SOURCE_CHECK 为本报告类别，不声称该 Lean 文件中存在同名字面标记。
- 即使同域更强库生产者已支付目标不等式，也不能据此宣称陈述完全遵循原证明或原文全验证。

### DE-SOURCE-CHECK-EXCEPTION

SOURCE_CHECK：LWD (2.4)–(2.8)、McCurley Gamma 输入与原 c1 区域的来源及严格边界仍需原文逐式核对。本树的恒等式、传输和固定实源分类不构成原页已验证的证据。

- **源码锚点**：`LiuWang/Proof/SourceRoute/Exception/Restart/OriginalV1/PrincipalIdentity.lean:3`
- **消费者**：`LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1.l24_low_of_gamma_estimate; LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1.l24_high_of_gamma_estimate; LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1.l25_induced_of_gamma_estimate; LiuWang.Proof.SourceRoute.Exception.Restart.paper_source_original_zero_iff`
- 完整零点和的源码归属见 LiuWang/Proof/SourceRoute/Exception/Restart/OriginalV1/ZeroTransport.lean:5；LWD (2.5)–(2.6) 及两个 McCurley 输入见 LiuWang/Proof/SourceRoute/Exception/Restart/OriginalV1/PrincipalIdentity.lean:3。
- 需要核普通 L 函数重数、导出字符 Euler 修正符号、δ=0/1 与 δ=2、σ∈(1,1.15)、|t|<1 与 |t|≥1、原 c1 窗与种子量词；当前树没有原文扫描证据。
- docs/STATUS.md:20 的字面 SOURCE_CHECK 具体指 (2.29)、(2.37)，属 LowSum 等模块，列在 coverage 中交叉引用，不伪装成本目录已定位的同名印式缺口。

## 已有生产者：明确排除的伪缺口

### DE-CLOSED-PRINCIPAL

hprincipal 不是新数学缺口：同树普通主字符预算 ≤7000 y^(4(1−α))log(y)^(6α)+51log(y)^3，原高 α 同域成立；由 log y≥1、7000≤11402、51log³≤16541log⁶及剩余项非负，可推出 principalSevenBound。现缺的是原消费者的导入/标量连接与原证明来源验收，不是主字符密度定理。未修改 Lean，也未编译该适配。
- 生产者：`LiuWang/Proof/GlobalZeroDensity/MeanInterpolation/Continuation/OrdinaryBudget.lean:112`
- 消费者：`LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.family_sourceSeven_from_original_inputs`

### DE-CLOSED-NONPRINCIPAL-GAMMA

l25 的 hgamma=0.3918 已有同域更强生产者：gammaDifference_le_four_fifteenths 给 4/15，利用 gammaDifference_eq 与 kappa_eq，4/15<0.3918。包括 induced/imprimitive 转移；不因 OriginalV1 仍把 hgamma 写成参数而列为数学缺口。
- 生产者：`LiuWang/Proof/ZeroRegionFamily/Sharp/Gamma.lean:114`
- 消费者：`LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1.l25_primitive_of_gamma_estimate; LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1.l25_imprimitive_of_gamma_estimate; LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1.l25_induced_of_gamma_estimate`

### DE-CLOSED-CHEN11-12

Chen (11)、(12) 所需 Q 边界已经用平方因子计数、Abel 与原常数比较给出，Titchmarsh 旧消费者的 hchen11/hchen12 不再计缺口；最新 ChenArithmetic.Consumer 无这两项前提。
- 生产者：`LiuWang/Proof/SourceRoute/Density/Restart/OriginalV1/ChenArithmetic/QBoundary.lean:46`
- 消费者：`LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.ChenArithmetic.equation_3_40; LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.ChenArithmetic.equation_3_41_at_source_shift`

### DE-CLOSED-336

原实 cutoff N=|1/2+it|/2（含 t=0 时 N=1/4）及 (3.36) 已有实数 cutoff Euler–Maclaurin 生产者；zeta_inputs 消除了 hzmax、hzmean、h336，不应再报缺口。
- 生产者：`LiuWang/Proof/SourceRoute/Density/Restart/OriginalV1/Critical336/OriginalCutoff.lean:76`
- 消费者：`LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.Critical336.zeta_inputs`

### DE-CLOSED-MEAN-ENDPOINTS

GlobalZeroDensity.Sharp.actual_detector_lemma_3_4、MeanInterpolation.actual_source_3_45、actual_lemma_3_5 均有同域无额外解析前提的生产者。分别与 DE-DENS-CHEN24/14 的字面中间输入区分；禁止宣称原链缺口推出这些终点仍未证。
- 生产者：`LiuWang/Proof/GlobalZeroDensity/MeanInterpolation/Consumer.lean:45`
- 消费者：`LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.Critical336.lemma_3_5_with_zeta_paid`

### DE-CLOSED-LOW-ALPHA

全族 T7 的原低 α 分支已有生产者，q=1、2 无非主字符也已处理；缺口集中在 Chen 非主高 α 定量输入。
- 生产者：`LiuWang/Proof/DirichletZeroCount/Applications/LowAlpha.lean:89`
- 消费者：`LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.family_sourceSeven_from_original_inputs`

### DE-CLOSED-TRANSPORT

Euler 主/非主导出修正、有号完整零点和、原窗普通 L 重数到本原字符的等价与高度单调均已提供；原窗成员资格只是定义/域条件。
- 生产者：`LiuWang/Proof/SourceRoute/Exception/Restart/OriginalV1/OriginalWindows.lean:90`
- 消费者：`LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1.original_window_sum_transport; LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1.original_window_count_le_conductor`

### DE-CLOSED-FIXED-SOURCE

给定原域实际实二次源后，原窗内零点的字符/模数/位置分类、单重性、槽 Subsingleton、非诱导模数无零和主论文 N≥exp3100 的实例化均已提供。PaperSource 是此分支的条件，不意味着必须证明例外零无条件存在。
- 生产者：`LiuWang/Proof/SourceRoute/Exception/Restart/Family.lean:72`
- 消费者：`LiuWang.Proof.SourceRoute.Exception.Restart.fixed_source_characterization; LiuWang.Proof.SourceRoute.Exception.Restart.paper_source_original_zero_iff`

### DE-CLOSED-REPULSION

已有原种子排斥到 cap(N,0.3221)、保留计数为零及已诱导模数精确计数等式，不把 hdiv 或给定种子当作未证明数学输入。
- 生产者：`LiuWang/Proof/SourceRoute/Exception/ExactCount.lean:43`
- 消费者：`LiuWang.Proof.SourceRoute.Exception.paper_source_familyCount_exact`

## 两条终端链的判断

**Density**：`complete_family_sourceSeven_from_original_inputs` 的 hprincipal 可由现成同域强界加标量比较支付；hchen 仍是实际非主全族原密度输入。`source_high_count`（`Density/Restart/SourceParameters.lean:44`）仅在 α∈[19/20,1] 产生偏移 a,U 上的计数母式；`produced_product_count_PV`（`Density/Restart/ProductCount.lean:57`）已支付 PV 与右边界，但 `productHorizontalCost` 仍含 `familyMaximum`，不能把有限性/最大值存在当数值支付。此受阻链统一归入 DE-DENS-CHEN，不另加“水平边”“左均值”“Jensen”“T7”四份重复缺口。

**Exception**：原 Euler 修正与普通 L 零点重数传输已经闭合；非主 Gamma 0.3918 可由库中 4/15 同域估计支付。主 ζ 的 δ=2 高低两个严格 Gamma 输入仍未付。固定真实实种子时，`fixed_source_characterization` 与 `paper_source_original_zero_iff` 已完成分类；不能从“若有实种子”跳到“任意原区域零点必为实种子”。`PaperAbsence.no_paper_source_re_le` 实际只给 R24 cap（`LiuWang/Proof/WeightedLowZeros/Continuation/PaperAbsence.lean:20`），较窄区域不能代原 c1。DE-EX-ORIGINAL-REGION 是跨模块共同的原域义务；不把例外零存在性本身列为必须成立的输入。

## 覆盖与复核

- 两个指定子树共 87 个 Lean 文件：已做声明/显式前提/依赖静态检索；逐路径、行数及 SHA-256 见 JSON 的 coverage。并精读最新 OriginalV1 消费者、种子分类和关键同树生产者。覆盖统计不表示每条证明都独立重放。
- 同树排查包括 GlobalZeroDensity/Sharp、MeanInterpolation/Continuation、NonprincipalDensityAdvance/Means、DirichletZeroCount/Applications、ZeroRegionFamily/Sharp 与 ApplicationScale、WeightedLowZeros，以及暴露同一原域输入的 LowSum/ThirdArc 消费者。
- 精确源码行锚在写入前检查存在；JSON 校验字段、ID 去重、可解析性。未用编译结果冒充来源核查。
- 原边界/量词不能改：严格/闭左边界分开；y 与 q·y 不混同；所有非主字符不缩为本原字符；普通 L 重数不能变成不计重零点集合；`∀u≥0` 不能变成有限窗口。
- 数学上有现成更强生产者的条目只标“已付可适配”，不新增替代路线、不修改代码；其原证明归属仍由 SOURCE_CHECK 单独验收。
