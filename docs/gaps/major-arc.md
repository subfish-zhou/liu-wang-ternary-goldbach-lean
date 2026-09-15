# 主弧源码缺口审查（普通支与例外支）

## 结论与口径

**当前不能把严格原 Liu–Wang 主弧路线报为完成。** 同树已经支付两个固定 ν 积分、两个原有限头、1961 有限和、纯例外导子母和/临界常数，以及选定 R24 源路径的混合母和数值。例外整除模数上的 retained 低零和也有完全匹配生产者，不能再列缺口。

本账列 **7 个审查记录**，混合了共同上游、当前预算参数和原对象合装；**不是 7 个互相独立的原数学难题**。最短消费者边界如下：

- 普通当前整主弧 `ordinary_major_lower_of_finite_head`：低和、高和、`1/3` 次幂有限头预算。
- 原普通算术 `I12_original_arithmetic_consumer` / `R14_bound`：原 `hRS` 尚需生产者；固定积分与原有限头不是缺口。
- 例外整主弧 `caseII_of_original_low_high_and_ordinary`：`h987`、`hphi`、`hordinary`、高和；显式 retained 低和输入已有同树生产者。
- 最新固定宽窗 `OriginalV1`：六项分解和实际有限和已有，尚不能用旧窄 R24 终端替代原宽窗分支合装。

源码快照：唯一主树 `/home/azureuser/liu-wang-ternary-goldbach-lean`，`main` 指向 `7e236a0008bf1ac1d4a7b923a8a4a34342f87315`。只读检查 Lean 与同树生产者，未编译、未启动证明/编码 CLI、未开分支或工作树。下文“已证”仅指源码含证明体且匹配消费对象，不冒充本次新内核验收。

记 `P=sourceP N`、`L=sourceL N`；一切生产者必须保留原 `N≥exp(3100)`、截断、导子和重数域。`hN`、`Odd N`、局部分支见证并非未付数学估计。

## 当前未付输入、预算和连接

### MA-LOW · 共同上游／原证明分支输入与连接

普通支低零和的实际分支输入仍须交付并接到主弧；不能把消费者对全部 q 的 hlow 当作无条件定理。已有 original_low_sum_exhaustive 把低和归约到高实部种子的 c1 上界，original_low_sum_of_short_absence 另显式保留短窗无零 hshort 与非实种子 hcomplex。低和算术积分与种子分支不应重新计成主弧独立缺口。

- **源码**：`LiuWang/Proof/SourceRoute/MajorOrdinary/Continuation/IntegralCertificates/FiniteHeads/Restart/QuadraticArithmetic.lean:189`
- **具体消费者**：`LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart.ordinary_major_lower_of_finite_head；LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart.OriginalV1.I12_original_arithmetic_consumer`
- **假设与生产者核对**：
  - N ≥ exp(3100)，Odd N，∀q∈denominators(sourceP N)，lowWeightSum N q ≤ 0.0194/sourceL N。
  - 共同上游消费者：LiuWang/Proof/SourceRoute/LowSum/Continuation/Restart/NoExceptionAssembly.lean:83 的 original_low_sum_exhaustive 仍要求 hc1；:109 的 original_low_sum_of_short_absence 要求 hshort、hcomplex。
  - lowWeightSum 是 sourceT 截断后再取 |Im ρ|≤omegaCutoff 的有限和；须用同树 values_low_eq_filter/omegaCutoff_le_sourceT 桥接 lowSum，不能忽略截断及重数。
  - 本记录按共同上游边界记账，不断言该边界内所有局部零区间/计数引理均缺失。

### MA-HIGH · 共同上游／原门槛定量输入

原门槛 N≥exp(3100) 下统一 highSum ≤0.0126 q/L^4 尚未在本次定位的实际消费者链中封口。最新 Source3536 消费者仍带 Theorem 7 密度输入、随高度一致的谱分支，以及 zeroTail；小高度支还留实际双积分。它是普通主弧和例外主弧共享的高零和输入，不是第二或第三整弧估计。

- **源码**：`LiuWang/Proof/SourceRoute/MajorException/Continuation/CriticalCertificate/SourceConsumption/Restart/Consumer.lean:91`
- **具体消费者**：`LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.caseII_of_original_low_high_and_ordinary；LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart.ordinary_major_lower_of_finite_head；LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.OriginalV1.I16_original_sum / I17_original_sum / I19_original_sum`
- **假设与生产者核对**：
  - ∀q≤P（例外混合项只需 d.modulus∣q），WeightedHighZeros.highSum N q ≤0.0126*q/L^4。
  - 原主弧 highWeightSum 用严格 omegaCutoff<|Im ρ|，WeightedHighZeros.highSum 的闭高窗可作上界；LiuWang/Proof/SourceRoute/MajorException/Continuation/CriticalCertificate/SourceConsumption/Restart/MotherTransport.lean:39 已证明对应 highMother_le_closed_high，不能把边界改动算作新分析定理。
  - 共同上游：LiuWang/Proof/SourceRoute/HighSum/Continuation/Payment/Checked/Restart/OriginalV1/Source3536/Assembly.lean:35、:52 保留 hT7、hcase、zeroTail 和小高度积分。
  - 同树 WeightedHighZeros.highSum_le_large_log（LiuWang/Proof/WeightedHighZeros/LargeLog.lean:115）确有完整界，但要求 N≥exp(100000000)，不能支付 exp(3100) 指标。

### MA-RS · 共同上游／原证明算术输入

Rosser–Schoenfeld 的实际整数比值界 q/φ(q)≤ν(q) 仍为假设。ν 的正性、单调性和固定 ν 积分已有证明，不会自动给出整数比值不等式。该义务被原普通支 I12/R14 与例外导子数值比较共同使用；只计一次。

- **源码**：`LiuWang/Proof/SourceRoute/MajorOrdinary/Continuation/IntegralCertificates/FiniteHeads/Restart/OriginalV1/OriginalArithmetic.lean:88`
- **具体消费者**：`LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart.OriginalV1.I12_original_arithmetic_consumer；LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart.OriginalV1.R14_bound；LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.actual_mixed_totals_paid；LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.caseII_of_original_low_high_and_ordinary`
- **假设与生产者核对**：
  - 原路线 hRS：∀q:ℕ，3≤q→(q:ℝ)/(q.totient:ℝ)≤nu q。
  - 例外 hphi 只需同一个实际导子 r 上的 r/φ(r)≤ν(r)，不能把全域 hRS 与这个实例重复计数。
  - I12_no_RS、I14_no_RS 已有不使用 hRS 的估计，但这是已证替代算术路径；严格原证明任务不能据此宣称原 hRS 证明已补。
  - 同树全量 Lean 文本检索 q/φ、nu、2.50637 后，相关精确签名均停留在假设或条件运输；未定位无条件原域生产者。

### MA-SMALL · 共同上游／原证明有限覆盖输入

例外导子 r≥987 仍由外部 h987 提供；必须补齐实际原实零区域内的剩余小导子排除，不能把“有若干小导子证书”当成全覆盖。大导子有效 L(1,χ) 与零间距生产者已经存在，故缺口不是重新证明全部有效 L 值理论。

- **源码**：`LiuWang/Proof/SourceRoute/MajorException/Continuation/CriticalCertificate/SourceConsumption/Restart/Consumer.lean:94`
- **具体消费者**：`LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.actual_mixed_totals_paid；LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.caseII_of_original_low_high_and_ordinary；LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.actual_pure_integrals`
- **假设与生产者核对**：
  - 实际 exceptionalValues 见证、q≤P，需要 987≤chi.conductor。
  - 已检同树 Through64.lean:39、VerifiedScan/Batch65_80.lean:22 与 Prime163.lean:35：有连续小段和孤立实例，未给出全部 r<987 的覆盖。
  - LiuWang/Proof/SourceRoute/MajorException/Continuation/CriticalCertificate/SourceConsumption/ActualGap.lean:27 的 actual_exceptional_gap 在 h987 下已从 ExceptionalZeroGap.real_primitive_local_zero_gap 产出 π/(0.4923√r(log r)^2)≤1−β，故不另立 hgap 缺口。

### MA-QHEAD · 预算参数／未付有限证书（非新增原义务）

当前 no_RS 普通整主弧消费者仍要求 totientMoment 100000 (1/3)≤4.01。该特定三分之一次幂有限头未找到同树生产者；已证的是 1/6 与 7/6 两个不同有限头，不能相互冒名。但 4.01 是当前二次项割线预算所选的充分常数，不应转写成原论文必需新增引理。严格原路线仍应交付实际 I13 原界或接上等价充分算术支付。

- **源码**：`LiuWang/Proof/SourceRoute/MajorOrdinary/Continuation/IntegralCertificates/FiniteHeads/Restart/QuadraticArithmetic.lean:154`
- **具体消费者**：`LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart.I13_of_finite_head；LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart.ordinary_major_lower_of_finite_head`
- **假设与生产者核对**：
  - hhead：totientMoment 100000 (1/3)≤4.01。
  - 该 hhead 与 MA-LOW/MA-HIGH 合用推出 ‖I13‖≤0.0016 N² 及 majorIntegral.re≥0.5437 N²。
  - 同树精确对象与 4.01 检索只见 QuadraticArithmetic 中的条件消费者；WholeHeads.lean:108 的两个已证头是另外的指数。
  - 记录的是现有路径的预算输入，不把它与未定位的原 I13 算术封口机械相加成两个独立数学缺口。

### MA-ORDREM · 预算接口背后的原证明有符号余项义务

例外情形的 ordinaryIntegral（删去实际例外零后的三个普通交互项）还需原证明的有符号总下界。caseII 消费者把 −9e−8 N² 下界直接作为 hordinary；未找到该实际积分的数值生产者。9e−8 只是现有合装的充分预算，不能反推“原证明必须逐项达到此加强界”。

- **源码**：`LiuWang/Proof/SourceRoute/MajorException/Continuation/CriticalCertificate/SourceConsumption/Restart/Consumer.lean:96`
- **具体消费者**：`LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.caseII_of_original_low_high_and_ordinary；LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.major_lower_without_mixed_mothers`
- **假设与生产者核对**：
  - hordinary：−(0.00000009*N²)≤(MajorException.ordinaryIntegral N).re。
  - 对象定义：LiuWang/Proof/SourceRoute/MajorException/AllInteractions.lean:18、:52；不是 MajorOrdinary.I12/I13/I14 的未删全零包。
  - 必须覆盖所有 q≤P，而不只是例外导子整除的模数；低和在整除分支已有删除生产者，非整除分支/选定源一致性须纳入实际普通项总账。
  - 若按原常数及有符号余量重新合装，应支付原实际余项而非固定要求这个预算接口；无条件模型下界不能代替实际积分。

### MA-PAPER-ASSEMBLY · 原证明对象与分支／待连接合装

最新 OriginalV1 已把同一个 PaperSource 的六个原交互项做到逐弧恒等式和实际有限模数和界，但尚未找到这些原对象通往原主弧最终数值下界的完整消费者。旧 Restart.Consumer 的整主弧结论从较窄 R24 exceptionalValues 见证出发，不能直接冒充所有原 PaperSource 的完成。需要实际分支覆盖、原六项与整弧对象的连接、原数值支付和普通余项统一合装；这是连接工作包，不把已证六项 Hölder/有限和重新列缺口。

- **源码**：`LiuWang/Proof/SourceRoute/MajorException/Continuation/CriticalCertificate/SourceConsumption/Restart/OriginalV1/SourceSums.lean:66`
- **具体消费者**：`LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.OriginalV1.I15_original_sum / I16_original_sum / I17_original_sum / I18_original_sum / I19_original_sum / I110_original_sum；LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.caseII_of_original_low_high_and_ordinary`
- **假设与生产者核对**：
  - OriginalV1 固定 PaperSource：d≤P、datumL d e=0、Im e=0、Re e<1、1−1/(9.645908801 log P)<Re e。
  - 较旧路径的 exceptionalValues 输入是 R24 区域；LiuWang/Proof/SourceRoute/MajorException/Continuation/CriticalCertificate/SourceConsumption/Restart/SourceTotal.lean:33 只证明由这个窄见证产生 PaperSource 的方向，不能倒推宽窗见证必在 R24。
  - LiuWang/Proof/SourceRoute/MajorException/Continuation/CriticalCertificate/SourceConsumption/Restart/OriginalV1/SixTerms.lean:77 已证明 same_source_six_arcs；SourceSums 的 I15/I18/I110 无 low/high 假设，I16/I17/I19 的 retained low 输入已有同树生产者、高和归入 MA-HIGH。
  - 统一常数与导子域的未付输入分别归入 MA-RS、MA-SMALL、MA-ORDREM，不重复计数；按原分支进行的纯连接与数学支付仍须分报。

## 已付反例清单：不能重新开缺口

### MC-INTEGRALS

两个原固定积分已证：∫[10^5,10^10] x^(−11/6)ν(x)^2≤0.0025，及指数−5/6的积分≤8794。

- 证据：`LiuWang/Proof/SourceRoute/MajorOrdinary/Continuation/IntegralCertificates/Consumers.lean:47`
- 生产者：both_original_fixed_integrals；LowIntegral.original_low_fixed_integral(:84)、HighIntegral.original_high_fixed_integral(:46)
- 验收边界：源码有完整生产者；本次未重编

### MC-HEADS

两个原有限头已证：totientMoment 100000 (1/6)≤3.2842，(7/6)≤69.9802；经实际算术 soundness、分块、WholeHeads 合装，不是仅裸数据。

- 证据：`LiuWang/Proof/SourceRoute/MajorOrdinary/Continuation/IntegralCertificates/FiniteHeads/WholeHeads.lean:108`
- 生产者：both_original_finite_heads / original_first_head / original_second_head
- 验收边界：源码已证；不可误列为 hhead(1/3) 的生产者

### MC-1961

式(4.5)后的 q≤1000 Möbius–totient 有限和≤1961 已证且已被 OriginalV1.TotientTail 消费。

- 证据：`LiuWang/Proof/ArithmeticBounds/Main.lean:58`
- 生产者：sum_moebius_totient_square_le_1961；消费者 LiuWang/Proof/SourceRoute/MajorOrdinary/Continuation/IntegralCertificates/FiniteHeads/Restart/OriginalV1/TotientTail.lean:79
- 验收边界：已付有限头；余下 hRS 与尾运输不可倒算为有限头缺口

### MC-NORS

I12_no_RS 给原 0.1108 N²、I14_no_RS 给原 0.00002 N²；相应母和、尾估计已有实质证明。

- 证据：`LiuWang/Proof/SourceRoute/MajorOrdinary/Continuation/IntegralCertificates/FiniteHeads/Restart/SourceMoments.lean:69`
- 生产者：LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart.I12_no_RS；LiuWang/Proof/SourceRoute/MajorOrdinary/Continuation/IntegralCertificates/FiniteHeads/Restart/HigherConsumers.lean:78 的 I14_no_RS
- 验收边界：算术侧已付；仍条件于原低/高零和；不是整主弧无条件完成

### MC-RETAINED

例外导子整除时，实际 retainedSum≤8.2e−10/L 已有完全匹配的生产者，消费者 hlow 不应列作独立数学缺口。

- 证据：`LiuWang/Proof/SourceRoute/LowSum/Continuation/InducedException.lean:59`
- 生产者：LiuWang.Proof.SourceRoute.LowSum.Continuation.induced_retained_weighted_bound
- 验收边界：hN、hq、同一个 PaperSource、d∣q 下已证；未假装覆盖非整除全普通项

### MC-GAP

实际例外零的定量间距已有生产者；h987 留在 MA-SMALL。

- 证据：`LiuWang/Proof/SourceRoute/MajorException/Continuation/CriticalCertificate/SourceConsumption/ActualGap.lean:27`
- 生产者：actual_exceptional_gap
- 验收边界：原 h987 域下已证；非全小导子覆盖

### MC-PURE

纯例外项的模数母和、导子极值证书和原数值常数已落实：原预算 0.000021、0.00108、0.09403，现有更强预算 0.00002099、0.0010299、0.093965。

- 证据：`LiuWang/Proof/SourceRoute/MajorException/Continuation/CriticalCertificate/PureCost.lean:148`
- 生产者：pure_decimal_payment / actual_pure_integrals_numeric；LiuWang/Proof/SourceRoute/MajorException/Continuation/PaidMass.lean:29 的 sourceArithmetic_paid
- 验收边界：在真实例外见证、hphi、h987 域内已有源码证明；不另列母和或临界点数值缺口

### MC-MIXED

旧 R24 实际选定源路径的三个混合项已做完规范化与数值母和，mixedBudget 为 3e−8、2e−8、0.00008452，且证明不超过原预算。

- 证据：`LiuWang/Proof/SourceRoute/MajorException/Continuation/CriticalCertificate/SourceConsumption/Restart/Consumer.lean:40`
- 生产者：actual_mixed_integrals_paid；LiuWang/Proof/SourceRoute/MajorException/Continuation/CriticalCertificate/SourceConsumption/Restart/DecimalPayment.lean:101 的 analyticCost_numeric
- 验收边界：仍需 h987、hphi、高和；低和已可从 MC-RETAINED 交付。不是新的三项独立缺口，也不等于宽 PaperSource 分支的数值合装

### MC-ORIGINAL-SIX

固定同一个宽窗 PaperSource 的六项逐弧恒等式、character 展开、Hölder 界和 q≤P 且 d∣q 的有限和已经存在。M、D 等局部上界参数有上游实例，不是新数学公理。

- 证据：`LiuWang/Proof/SourceRoute/MajorException/Continuation/CriticalCertificate/SourceConsumption/Restart/OriginalV1/SixTerms.lean:77`
- 生产者：same_source_six_arcs；LiuWang/Proof/SourceRoute/MajorException/Continuation/CriticalCertificate/SourceConsumption/Restart/OriginalV1/SourceSums.lean:111 的 I15_original_sum 等
- 验收边界：实际有限对象源码已证；终端原数值及全分支合装见 MA-PAPER-ASSEMBLY

### MC-EXPANSION

主弧完全展开、I11 的数值下界、展开误差及 prime-power-removal 已被实际主弧下游消费者调用，不是本报告新列的数学假设。

- 证据：`LiuWang/Proof/SourceRoute/MajorOrdinary/Assembly.lean:31`
- 生产者：majorIntegral_lower / primeCount_lower；LiuWang/Proof/SourceRoute/MajorException/Continuation/CriticalCertificate/SourceConsumption/Restart/Consumer.lean:79 的 source_expansion_error_payment
- 验收边界：本次核对调用与消费者签名；未对全部共同底层依赖做独立内核重放

## 整弧依赖、共同上游与覆盖

`MajorOrdinary.Assembly.lambdaCount_lower` / `primeCount_lower` 保留 M2、M3 两个实际积分，是把主弧结果接到全圆/表示数时的**整弧依赖**；本地 `majorIntegral_lower` 和两个主弧数值消费者不以“第二/第三整弧已经完成”为前提。低/高零和、密度、RS、例外源小导子则是**共同上游**。父级总账应按相同对象、量词及域合并，不能按导入模块或被阻节点加总。

`hhead≤4.01` 和 `hordinary≥−9e−8N²` 属当前充分预算接口。它们不是原论文自动新增的必需命题；可以沿原有符号全账接等价充分界，但不能因此把尚未交付的实际普通余项报为完成。局部 Hölder 中任取的正上界 `M` 则已有 `ordinaryMass_le_original` 等实例，不是额外数学输入。

- **快照与验收边界**（`LiuWang/Proof/SourceRoute/MajorOrdinary/Assembly.lean:31`）：唯一主树 main；读取 .git HEAD 指向 7e236a0008bf1ac1d4a7b923a8a4a34342f87315。源码只读；未编译、未启动 CLI/worker、未读取旧报告作为完成证据。只写本报告两文件。
- **普通原算术消费者**（`LiuWang/Proof/SourceRoute/MajorOrdinary/Continuation/IntegralCertificates/FiniteHeads/Restart/OriginalV1/OriginalArithmetic.lean:88`）：I12 原算术与 R14 原尾路线保留 hRS；固定积分和原两个有限头已付。no_RS 路线保留低/高零和及 I13 的预算有限头。
- **普通当前整主弧消费者**（`LiuWang/Proof/SourceRoute/MajorOrdinary/Continuation/IntegralCertificates/FiniteHeads/Restart/QuadraticArithmetic.lean:189`）：ordinary_major_lower_of_finite_head 的显式数学输入全部列入 MA-LOW、MA-HIGH、MA-QHEAD；hN、hodd 是目标域，不是缺口。
- **例外当前整主弧消费者**（`LiuWang/Proof/SourceRoute/MajorException/Continuation/CriticalCertificate/SourceConsumption/Restart/Consumer.lean:91`）：caseII 的 h987、hphi、hordinary、高和分别列入 MA-SMALL、MA-RS、MA-ORDREM、MA-HIGH；retained hlow 经 MC-RETAINED 已付；hr 是该分支见证，不要求无条件存在例外零。
- **例外最新 OriginalV1 消费者**（`LiuWang/Proof/SourceRoute/MajorException/Continuation/CriticalCertificate/SourceConsumption/Restart/OriginalV1/SourceSums.lean:66`）：六个实际有限和及逐弧分解均核过签名/证明；不得把旧 R24 母和消费者和新宽窗 PaperSource 对象静默合并。
- **有限证书生产者**（`LiuWang/Proof/SourceRoute/MajorOrdinary/Continuation/IntegralCertificates/FiniteHeads/WholeHeads.lean:105`）：已追 ArithmeticSoundness、BlockSoundness、Block0000–Block0098 的合装引用与 WholeHeads 的实际结论；未逐条重新内核验算。1/3 预算头与已付 1/6、7/6 头区别列账。
- **共同低和上游**（`LiuWang/Proof/SourceRoute/LowSum/Continuation/Restart/NoExceptionAssembly.lean:109`）：普通短窗无例外/非实种子分支仍是输入边界；例外整除 retained 生产者另已匹配。深层零区间、密度、计数缺口由共同上游报告去重，本报告不将调用节点数当独立问题数。
- **共同高和上游**（`LiuWang/Proof/SourceRoute/HighSum/Continuation/Payment/Checked/Restart/OriginalV1/Source3536/Assembly.lean:52`）：核定实际剩余积分、zeroTail、hT7 和谱支；已检查 LargeLog 的更高阈值，拒绝降格为原 exp(3100) 完成。
- **小导子现有生产者**（`LiuWang/Proof/SmallConductorExpansion/Continuation/VerifiedScan/Batch65_80.lean:22`）：与 Through64、163 证书一并核对，避免沿用旧“只到3、4”的说法；本报告不单独声称完整小导子计数或最优剩余集合。
- **整弧依赖与共同上游**（`LiuWang/Proof/SourceRoute/MajorOrdinary/Assembly.lean:45`）：lambdaCount_lower/primeCount_lower 还显式带 M2、M3 的实际积分：这是全圆积分恢复表示数所需的另外两整弧估计，不是证明主弧局部下界的前置。低/高零和、密度、RS、例外小导子等则是跨弧共享上游，不能重复计费。
- **原目标保持**（`LiuWang/Proof/SourceRoute/MajorException/Continuation/CriticalCertificate/SourceConsumption/Restart/Consumer.lean:91`）：保持 N≥exp(3100)、奇数及最终三奇素数目标；主弧报告不宣称已得到 I(N)>0 或最终无条件定理。预算参数和原证明义务按 kind 分开。

## 检索与审查限制

逐签名追查 `MajorOrdinary`、`MajorException` 的 Assembly/Consumer/OriginalV1 出口，向同树回查固定积分、有限块及尾、源删除、有效零间距、小导子覆盖和低/高零和。对精确消费者名、`4.01`、`totientMoment 100000 (1 / 3)`、`nu`/`2.50637` 及相关 low/high 常数作全树 Lean 文本交叉定位。未以 README、旧 STATUS、旧报告或 `#print axioms` 命令文本当作执行结果。未对所有底层导入做新内核检查，也未重新核验原论文 PDF；“原”这里明确指当前源码的原式对象/消费者路线，不额外宣称来源验收完成。

仅生成 `docs/gaps/major-arc.md` 与 `docs/gaps/major-arc.json`。JSON 各记录的 `source` 均在写入前按当前真实相对路径与行号验证。
