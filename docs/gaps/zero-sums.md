# SourceRoute 低零和与高零和：当前未付输入清单

## 口径与结论

- 依据唯一主工作树 `/home/azureuser/liu-wang-ternary-goldbach-lean` 的当前可读源码；main HEAD：`7e236a0008bf1ac1d4a7b923a8a4a34342f87315`。当前源码哈希清单保存在同目录 JSON 的 `coverage[file-coverage].files`。
- 覆盖 LowSum 的 69 个 Lean 文件、HighSum 的 239 个 Lean 文件，共 308 个；在 2732 个非隐藏项目 Lean 源文件中查找现有生产者。关键前沿及候选生产者精读，数值分块/探针不作执行验收。
- 去重后记录 **8 个剩余输入/残项工作包**，其中包含解析证明、有限高度验证、分支接线和 SOURCE_CHECK，不等于“8 个未证 lemma”。T1 已有条件生产者，不能与其 Gamma/RS 上游再算一次；T7 也不能按每个下游使用点重复计数。
- 只审查源码。未启动 CLI、未编译、未开分支或工作树、未修改 Lean。`AxiomCheck` 中的命令和旧证据都不充当本次通过记录。
- 仅讨论 Liu–Wang 的 `N ≥ exp 3100` 路线。保留原印式和 SOURCE_CHECK；不由局部付款推断完整高零界已闭，更不声称所有奇数已闭。

## 字面对象与去重规则

令 `L=log N`、`P=L^3`、`T=L^15`、`ω=3.36P/q`、`c1=9.645908801`、`q1=max(100000/q,10000 log q)`；参数定义见 `LiuWang/Proof/Interfaces/Main.lean:60`、`:64`、`:76`、`:80`。
`familyCount` 按字符与真实零重数计数，实部窗口左端闭；`strictFamilyCount` 左端严格。两者不能直接混同，当前树分别提供 T1 版本及需要的端点运输。

| 对象 | 实际公式/区间 | 处置 |
|---|---|---|
| Gamma-high | 带 `+1` 位移的 digamma 差，`1≤|t|`，严格 `<κ log|t|+0.3316` | ZS-GAMMA-HIGH |
| Gamma-low | 同一带位移函数，`|t|<1`，严格 `<0.0615` | ZS-GAMMA-LOW；不与高虚部合并 |
| RS | ζ 的 `0<Re z<1, |Im z|<1894438 ⇒ Re z=1/2` | ZS-RS；不是短高度字符排除 |
| T1 | `strictFamilyCount q (1−0.26213/log x) (x/q)≤4` | 已有条件生产者，归 Gamma/RS，不另计 |
| T7 | 全字符族 `familyCount≤B7`，`y≥q1` | 唯一 ZS-T7；主/非主生产者分别核验 |
| LowSum 短窗 | `|Imρ|≤P/q ⇒ Reρ<paperCap N` | ZS-LOW-SHORT |
| LowSum 非实种子 | `paperCap≤Reρ, Imρ≠0 ⇒ Reρ≤cap(1/c1)` | ZS-LOW-COMPLEX |
| HighSum zeroTail | 高度 `[ω,T]`，λ区间 `[0,1/c1]`，全族计数 | ZS-HIGH-ZEROTAIL |
| HighSum 短积分 | 高度 `[ω,q1]`，α区间 `[19/20,1−0.478/log(qy)]` | ZS-HIGH-SHORT；不是 LowSum 短窗 |

### T1 已接到哪里

生产者 `LiuWang/Proof/SourceRoute/LowSum/Continuation/Restart/OriginalV1/CountCap/Counts.lean:33` 的 `original_T1_strict_family_le_four`，在 `x≥8000000000, q≤x` 下，条件于恰好 RS、Gamma-high、Gamma-low，给出原严格 T1。闭计数版本 `closed_family_le_four` 在同文件第55行。
实际消费者 `LiuWang/Proof/SourceRoute/HighSum/Continuation/Payment/Checked/Restart/OriginalV1/HeightCases/Assembly.lean:15`、`:33` 中，T1 是对每个 `y∈[ω,T]` 的族上界。取 `x=q*y` 后字面相同；`q*y≥3.36P`、`(q*y)/q=y` 属已有尺度与普通代数接线，不另立数学缺口。此只读审查没有新增或编译这个封装。
`LiuWang/Proof/SourceRoute/HighSum/Continuation/Payment/Checked/Restart/OriginalV1/HeightCases/Payment.lean:12` 已逐高度分 FirstCase / SecondCase / ThirdCase，将旧“全高度固定同一 hcase”的入口替换为真正覆盖；因此 hcase 与三种分支都不再各开任务。

## 去重后的未付工作包

### ZS-GAMMA-HIGH — 未付解析输入

主字符移位 Gamma 的高虚部严格界；全部八种三零组合及严格/闭边界 T1 重复消费同一输入，合并计一次。

- **源码**：`LiuWang/Proof/SourceRoute/LowSum/Continuation/Restart/OriginalV1/CountCap/Counts.lean:33`
- **具体消费者**：`LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CountCap.original_T1_strict_family_le_four`

- 对所需的每个 x≥8000000000，∀t∈ℝ，1≤|t| → gammaHalfDifference (lwdSourceSigma x) t < stechkinConductorCoeff·log|t|+0.3316。具体前提在同文件:37。
- 令 κ=stechkinConductorCoeff，k=stechkinK，A(x)=(√3−1)/(7κ+2.4998/log x)，σ(x)=1+A(x)/log x。gammaHalfDifference σ t=(Re digamma((σ+it)/2+1)−k Re digamma((stechkinSigma σ+it)/2+1))/2。定义分别见 LiuWang/Proof/SourceRoute/LowSum/Continuation/Restart/OriginalV1/CaseIV.lean:15、18 与 LiuWang/Proof/SourceRoute/LowSum/Continuation/Restart/OriginalV1/PrincipalCases/Kernels.lean:14。
- 源参数定理 LiuWang/Proof/SourceRoute/LowSum/Continuation/Restart/OriginalV1/CaseIV.lean:20 已给 1<σ(x)≤1.02，不另算域缺口；HighSum 所需为每个高度 y 的 x=q*y。
- 同树 LiuWang/Proof/SourceRoute/Exception/Restart/OriginalV1/PrincipalIdentity.lean:78 的 gammaTerm 2 仍以同型 hgamma 为前提。函数经代数改写与此 +1 移位一致，kappa_eq 也已有，但这不是分析生产者。
- LiuWang/Proof/ZeroRegionFamily/Sharp/Gamma.lean:92 的 gammaDifferenceAt 只有奇偶位移 0/1，不是这里的位移2；其4/15或非主字符0.3918界不能直接替代。全树检索未见此严格界的无额外分析前提生产者。

### ZS-GAMMA-LOW — 未付解析输入

主字符移位 Gamma 的 |t|<1 严格常数界；不同于高虚部界，也不同于短高度零点排除。

- **源码**：`LiuWang/Proof/SourceRoute/LowSum/Continuation/Restart/OriginalV1/CountCap/Counts.lean:33`
- **具体消费者**：`LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CountCap.original_T1_strict_family_le_four`

- 对每个所需 x≥8000000000，∀t∈ℝ，|t|<1 → gammaHalfDifference (lwdSourceSigma x) t < 0.0615。参数与函数严格同 ZS-GAMMA-HIGH；具体前提在同文件:39。
- 非严格的 PrincipalCases/FarHeight.lwd_case_ii（LiuWang/Proof/SourceRoute/LowSum/Continuation/Restart/OriginalV1/PrincipalCases/FarHeight.lean:74）可由严格版本供给，不重复计数。
- LiuWang/Proof/SourceRoute/Exception/Restart/OriginalV1/PrincipalIdentity.lean:65 的 l24_low_of_gamma_estimate 同样保留 hgamma。Sharp/Gamma 的奇偶界不支付此移位2的0.0615界。

### ZS-RS — 未付外部验证输入

有限高度 ζ 零点验证输入；所有主字符槽的 Riemann–Siegel 型使用合并为一次。

- **源码**：`LiuWang/Proof/SourceRoute/LowSum/Continuation/Restart/OriginalV1/CountCap/Counts.lean:33`
- **具体消费者**：`LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CountCap.original_T1_strict_family_le_four`

- ∀z∈ℂ，riemannZeta z=0 → 0<z.re → z.re<1 → |z.im|<1894438 → z.re=1/2。高度与临界带端点均按严格不等式保留；同文件:35。
- LiuWang/Proof/SourceRoute/LowSum/Continuation/Restart/OriginalV1/CountedTriples/SelectedCosts.lean:15 的 principal_slot_RS 只将此假设变成非临界线主字符槽 |Imρ|≥1894438，不是验证本身。
- 全树当前可读项目源码检索未见该高度的无前提证明或可读验收证书生产者；AxiomCheck 中 #check/#print 指令不作为本次运行证据。

### ZS-T7 — 未付解析输入及待接线

原 T7 全字符族密度输入尚未闭合；endpoint、(2.26)、Source20、HeightCases 的相同 hT7 合并。追生产者后主要未付分析边为 Chen 非主字符族，主字符已有足够强的生产者待适配。

- **源码**：`LiuWang/Proof/SourceRoute/HighSum/Continuation/Payment/Checked/Restart/OriginalV1/HeightCases/Assembly.lean:33`
- **具体消费者**：`LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.HeightCases.highSum_small_height`

- 实际 hT7：∀α,y∈ℝ，1/2≤α → α<1 → max(100000/q,10000 log q)≤y → familyCount q α y ≤ B7(q,α,y)。全体模 q 字符、闭实部左边界、闭高度、实际零重数；不除以φ(q)。
- B7=16541(log y)^6+(17102+254231/log(qy))(q^3 y^4)^(1−α)(log(qy))^(6α)；LiuWang/Proof/DirichletZeroCount/Applications/LowAlpha.lean:15。
- LiuWang/Proof/SourceRoute/Density/Restart/OriginalV1/FamilyAssembly.lean:107 的 family_sourceSeven_from_original_inputs 将它归约成 hprincipal、hchen。hchen：3≤q → ∀β∈[1/2,1)，strictNonprincipalCount q β y ≤ (250359/log(qy)+5700)(q^3 y^4)^(1−β)(log(qy))^(6β)。其严格实部左界、闭高度、实际重数定义在 LiuWang/Proof/SourceRoute/Density/Restart/OriginalV1/ChenBoundary.lean:21，bound在:59，:98仅作严格到闭边界运输，不证明此分析估计。
- hprincipal 目标为 count(1:Character 1) α y ≤ 16541(log y)^6+11402 y^(4(1−α))(log y)^(6α)+3872 y^(4(1−α))(log y)^(8α−3)，仅在 α≥1/2+2 sourceDelta y 时需要。
- 现成 LiuWang/Proof/GlobalZeroDensity/MeanInterpolation/Continuation/OrdinaryBudget.lean:112 给 7000 y^(4(1−α))(log y)^(6α)+51(log y)^3。LiuWang/Proof/SourceRoute/Density/Restart/OriginalV1/AuxiliaryDomain.lean:31 已证 sourceDelta=Strip.delta。y≥10000 时 log y≥1，7000≤11402、51(log y)^3≤16541(log y)^6且剩余项非负，故足以支付hprincipal；只剩标量适配，未写/未编译该适配器。此复用不自动验收原论文内部每一箭头。
- 低α族界已有 LowAlpha.lean:89；q=1,2 非主族为空。不能用主字符计数≤B7冒充完整族和≤B7。ChenBoundary.lean:4 的原文假设核查提醒保留为 SOURCE_CHECK。

### ZS-LOW-SHORT — 分支数学输入及待接线

LowSum 无例外消费路径的短高度排除/分支证据尚未全面接上；不是要求对所有 q 无条件排除例外零。

- **源码**：`LiuWang/Proof/SourceRoute/LowSum/Continuation/Restart/NoExceptionAssembly.lean:109`
- **具体消费者**：`LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.original_low_sum_of_short_absence`

- N≥exp3100、0<q≤P 下，需要 ∀χ:Character q，∀ρ∈CompleteExpansion.zeroValues χ ω，|ρ.im|≤P/q → ρ.re<paperCap N，其中 paperCap=1−1/(9.645908801 log P)。hshort在同文件:111；与 |t|<1、ζ高度1894438均不同。
- 必须从所处的实际无例外分支获得此闭短窗中的无零证据；hN、hq本身不提供它。不能抹去已有例外源。
- 现成 LiuWang/Proof/SourceRoute/Exception/Restart/PaperApplication.lean:30 在给定 PaperSource N d e 且 ¬d.modulus∣q 时，提供同短窗非零结论；用零成员条件ρ.re<1排除pole后可供hshort。这个特定分支只需接线，不再新开分析缺口；一般无源分支没有在此消费文件中被生产/接入。
- 给定PaperSource且d.modulus∣q的分支已由 LiuWang/Proof/SourceRoute/LowSum/Continuation/InducedException.lean:43 支付 primed bound；PaperSource存在与否是分支数据，不能按假设名字自动计缺口。

### ZS-LOW-COMPLEX — 未付零区域输入

LowSum 高实部非实种子的原 c1 截断界；同树已有较弱/分支区域不足以支付全部范围。

- **源码**：`LiuWang/Proof/SourceRoute/LowSum/Continuation/Restart/NoExceptionAssembly.lean:109`
- **具体消费者**：`LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.original_low_sum_of_short_absence`

- N≥exp3100、0<q≤P 下，需要 ∀χ:Character q，∀ρ∈CompleteExpansion.zeroValues χ ω，paperCap N≤ρ.re → ρ.im≠0 → ρ.re≤cap N (1/9.645908801)。hcomplex在同文件:113；cap N a=1−a/log(3.36P)。输入paperCap用log P，输出cap用log(3.36P)，不能混淆。
- 同文件:85的完整hc1由hshort+hcomplex经original_high_seed_nonreal合成；hc1、family_tail_exhaustive、original_low_sum_exhaustive、最终0.0194/L和Jrho界都是下游，不另外计数。
- LiuWang/Proof/ZeroRegionFamily/Sharp/Consumer.lean:10 仅R20且χ≠1、非二次或|Imρ|≥1/2；LiuWang/Proof/ZeroRegionFamily/ApplicationScale/Continuation/Frontier/LowHeight.lean:79 仅原常数下二/三阶小高度分支，均不覆盖全部字符/所需非实高度。
- LiuWang/Proof/SourceRoute/Exception/PaperWindow.lean:27 的原种子排斥只限制别的、非共轭零，不限制种子自身实部，不能当hcomplex生产者。

### ZS-HIGH-ZEROTAIL — 未付残项及SOURCE_CHECK

HighSum 仍带从λ=0起的 zeroTail；有限K3付款未覆盖这段，保留 SOURCE_CHECK。

- **源码**：`LiuWang/Proof/SourceRoute/HighSum/Continuation/Payment/Checked/Restart/OriginalV1/HeightCases/Assembly.lean:15`
- **具体消费者**：`LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.HeightCases.highSum_large_height`

- zeroTail N q = ∫_{ω}^{T} y^(−2)[L/log(qy)·∫_{0}^{1/9.645908801} N^(−λ/log(qy)) familyCount q (1−λ/log(qy)) y dλ]dy；字面式 LiuWang/Proof/SourceRoute/HighSum/Continuation/Payment/Checked/Restart/OriginalV1/Source3536/Payment.lean:91。
- finiteK3区间是[1/9.645908801,0.36]，其0.0102654 q/L^4已有条件于T1的付款。original_height_zero_tail只做精确分拆，未付zeroTail预算。
- 这里的familyCount计入|Imρ|≤y全部零，包括低高度/实零；即使highValues排除了低高度，这个分部求和后计数也不是过滤后的highValues。不能从例外源实性或文件名推出zeroTail=0。
- 需要原路线对该实际积分的源核、补偿或定量控制；当前消费者没有给出并证明此段独立预算。本表不另造zeroTail=0或任意余量目标。ZS-LOW-COMPLEX即使补上，也不等于此全族尾积分已付。

### ZS-HIGH-SHORT — 未付转移及SOURCE_CHECK

(2.25)实际短高度积分到(2.27)印式预算的归一化转移未付；印式数值证书本身已付。

- **源码**：`LiuWang/Proof/SourceRoute/HighSum/Continuation/Payment/Checked/Restart/OriginalV1/Source27/Difference.lean:101`
- **具体消费者**：`LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source27.actualShort_le_literal_add_remainder`

- 短分支ω<q1=max(100000/q,10000 log q)。actualShort=∫_{ω}^{q1} y^(−2)∫_{19/20}^{1−0.478/log(qy)} N^(α−1)L familyCount q α y dα dy；LiuWang/Proof/SourceRoute/HighSum/Continuation/Payment/Checked/Restart/OriginalV1/Source27/Normalization.lean:16、36。与ZS-LOW-SHORT逐零排除不是同一输入。
- 现成确切上界actualShort≤(q/L^4)exactEnvelope；exactEnvelope=∫_{log(3.36L^3)}^{log(q q1)}K ds；K=L^4[(φ/q)(s/π−0.874)+φ(6.8423s+15)e^(−s)](e^(−0.478L/s)−e^(−L/20))，φ=φ(q)。Normalization.lean:27、106 保留实际φ。
- 已付印式scalar(L)=∫_{log(3.36L^3)}^{log(10000L^3 log(L^3))}I ds≤197/100000；I=L^4[s/π−0.874+(6.8423s+15)e^(−s)/700000]e^(−0.478L/s)。LiuWang/Proof/SourceRoute/HighSum/Continuation/Payment/Checked/Restart/OriginalV1/Source27/Literal.lean:14、37、44。
- 精确桥exactEnvelope=scalar+transferRemainder，R=∫_{lower}^{log(q q1)}(K−I)ds−∫_{log(q q1)}^{upper}I ds；Difference.lean:11、19、84。最新上界仍带R，实际短积分到印式0.00197 q/L^4的箭头没有支付；不把较强的R≤0或点态支配当作已知或额外必需任务。
- Difference.lean:110、117、125、133给φ/q≤1、1/q≤1/700000<φ(q)，主系数差非正而指数系数差严格正。不能把φ偷换成1/q，也不能由一个正项判定含负端点/尾段的完整R符号或论文定理错误；保留SOURCE_CHECK，不修印式。
- 同一个实际短积分在 LiuWang/Proof/SourceRoute/HighSum/Continuation/Payment/Checked/Restart/OriginalV1/HeightCases/Assembly.lean:43、LiuWang/Proof/SourceRoute/HighSum/Continuation/Payment/Checked/Restart/OriginalV1/Source20/Payment.lean:37 等下游重复出现，不另外计数。

## 已有生产者与关闭实例

下表中的“条件生产者”只说明条件推导链已存在，绝非声称相应上游假设已有证明；“待适配”也不是已编译。

### C-T1

- `LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CountCap.original_T1_strict_family_le_four`
- 源码：`LiuWang/Proof/SourceRoute/LowSum/Continuation/Restart/OriginalV1/CountCap/Counts.lean:33`
- 状态：条件生产者；上游三输入未付
- T1原严格窗strictFamilyCount q (1−0.26213/log x)(x/q)≤4已有条件生产者；product重数、严格槽、闭family与闭product版本均存在。仅剩同一RS、Gamma-high、Gamma-low，不独立重复计T1。

### C-COUNTED-DATA

- `LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CountedTriples.canonical_counted_data`
- 源码：`LiuWang/Proof/SourceRoute/LowSum/Continuation/Restart/OriginalV1/CountedTriples/Data.lean:32`
- 状态：已有生产者（源码审查，未重放）
- 真实带重数槽到本原字符标签已构造；CountedTriples/Cases.lean:75、110已路由八种组合。槽提取、共轭运输与结构字段不自动成为缺口。

### C-LOW-ROWS

- `LiuWang.Proof.SourceRoute.LowSum.Continuation.family_nine_rows`
- 源码：`LiuWang/Proof/SourceRoute/LowSum/Continuation/Counts.lean:52`
- 状态：已有生产者（源码审查，未重放）
- 实际九个密度表行已有生产者，已接入RowIntegrals的3e−13/L、6e−13/L付款；不是未付hrows。

### C-LOW-K1

- `LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.family_K1_exhaustive`
- 源码：`LiuWang/Proof/SourceRoute/LowSum/Continuation/Restart/KOneExhaustion.lean:91`
- 状态：已有生产者（源码审查，未重放）
- K1≤0.0104/L已闭；末段family_K1_last_actual用已有13计数仍付0.0001/L，不再等待旧入口的4计数前提。

### C-LOW-EXCEPTION

- `LiuWang.Proof.SourceRoute.LowSum.Continuation.induced_original_primed_bound`
- 源码：`LiuWang/Proof/SourceRoute/LowSum/Continuation/InducedException.lean:43`
- 状态：已有生产者（源码审查，未重放）
- 给定真实PaperSource且d.modulus∣q，扣源零权重后的lowSum≤8.2e−10/L；不宣称PaperSource处处存在。

### C-HIGH-BASE

- `LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source20.actual_source20_paid`
- 源码：`LiuWang/Proof/SourceRoute/HighSum/Continuation/Payment/Checked/Restart/OriginalV1/Source20/Decomposition.lean:171`
- 状态：已有生产者（源码审查，未重放）
- 真实初始质量及1/2..19/20积分已付exp(−90)/L^4，无T1/T7前提；不沿旧exp(−75)版本重复计缺口。

### C-HIGH-26

- `LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source26Certificate.actual_large_height_paid`
- 源码：`LiuWang/Proof/SourceRoute/HighSum/Continuation/Payment/Checked/Restart/OriginalV1/Source26Certificate/Payment.lean:13`
- 状态：条件生产者；T7未付
- (2.26)实际大高度积分到0.00031 q/L^4的数值/积分链已有，只共用ZS-T7。

### C-HIGH-32

- `LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.actual_source32`
- 源码：`LiuWang/Proof/SourceRoute/HighSum/Continuation/Payment/Checked/Outcome.lean:20`
- 状态：已有生产者（源码审查，未重放）
- λ∈[0.36,0.478]的实际积分已付(368/1000000000000000) q/L^4；各Checked分块不算独立数学输入。

### C-HIGH-K3

- `LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.HeightCases.finiteK3_paid`
- 源码：`LiuWang/Proof/SourceRoute/HighSum/Continuation/Payment/Checked/Restart/OriginalV1/HeightCases/Payment.lean:39`
- 状态：条件生产者；合并至Gamma/RS
- 逐高度First/Second/ThirdCase已分类并归一到0.0102654 q/L^4，只需T1；不再假设所有高度同属一个hcase。SecondCase另有0.0016界。

### C-HIGH-27-LITERAL

- `LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source27.scalar_uniform`
- 源码：`LiuWang/Proof/SourceRoute/HighSum/Continuation/Payment/Checked/Restart/OriginalV1/Source27/Literal.lean:37`
- 状态：已有生产者（源码审查，未重放）
- 印式scalar(L)≤197/100000已付；不等于含φ(q)的实际短高度积分已付。

### C-T7-PRINCIPAL

- `LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation.ordinary_principal_budget`
- 源码：`LiuWang/Proof/GlobalZeroDensity/MeanInterpolation/Continuation/OrdinaryBudget.lean:112`
- 状态：足够强的生产者；待适配，未编译验证
- 7000/51主字符计数界足以经非负性和常数比较供原hprincipal，delta对应已有定理；不另开主字符数学缺口。

## 覆盖与不重复计数矩阵

| 最新消费出口 | 仍保留/需要的输入 | 已不应再计的下游节点 |
|---|---|---|
| LowSum `original_low_sum_of_short_absence` | 真实无例外短窗排除、非实高实部种子 cap | `hc1`、tail integral、`0.0194/L`、Jrho 范数和是同一输入的后继 |
| LowSum `CountCap` 各 T1 版本 | 两个不同 Gamma 公式、同一 RS | 八种主/非主组合、槽抽取、本原运输、严格/闭计数各是已有链组件 |
| LowSum `induced_original_primed_bound` | 给定实际 PaperSource 与 inducing 分支 | 分支定理已付；不另设“必须处处存在例外源”的任务 |
| HighSum `HeightCases.highSum_large_height` | T1 的三个上游输入、T7、zeroTail | (2.20)、(2.26)数值、(2.32)、finiteK3标量不重复计 |
| HighSum `HeightCases.highSum_small_height` | 上行全部，加 actualShort 转移 | Source27 scalar 已付，不能重复立数值任务；也不能据此吞掉 transferRemainder |
| 两个 `primedHighSum_*` | 同上；例外零实性只是该分支还原条件 | 不重复开高零付款 |

普通条件 `N≥exp3100`、`NeZero q`、`q≤P`、积分端点顺序、`hlarge/hsmall`、所选零属于窗口、槽分离以及本原标签并不是数学缺口。只有缺少把实际分支送入相应条件的证据时，才保留具体工作包。

### 反查结论与边界

- **Gamma**：`gammaTerm 2` 的现成消费者仍携带同型输入；奇偶 Gamma producer 不覆盖此位移2公式。
- **T1**：完整八案到计数上界的条件链存在；重复把 T1 与 Gamma/RS 各算一次会高估缺口。
- **T7**：低 α 与主字符已有可复用生产者；Chen 非主字符族界未由边界运输定理支付。主字符充分界的适配不替代原路线源文验收。
- **短高度**：无源分支的逐零排除、含 φ 的实际积分、ζ有限高度验证是不同对象；相同“short/low”命名不构成合并理由。
- **zeroTail**：全族计数含实零/低零，不能用 highValues 的支撑或非实 cap 无声截去。
- **(2.27)**：已付印式 scalar，不等于已付含 φ 的 exactEnvelope；必须保留完整差额和负端点/尾段。单项系数方向不能判定完整差额符号。

## 验证范围

本交付检查 JSON 结构、唯一 ID、主 source 行号与具体声明对应，以及目标文件清单/哈希。它是当前源码依赖审计，不是 Lean 内核、数值计算或论文图像来源的重新验收。完整逐文件覆盖清单见 `zero-sums.json`，避免在 Markdown 中重复数百个数值分块名。
