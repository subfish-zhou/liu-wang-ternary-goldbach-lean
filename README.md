# Liu–Wang 三素数定理形式化（进行中）

Lean 4 解析数论与 Liu–Wang 原论文路线的公开源码快照。

> **本仓库尚未完成主定理证明，也尚未完成当前快照的全量集成验证。**
> 部分结果仍以未证明的数学命题为显式前提。公开源码、单个文件通过编译，均不等于这些前提已经消去。

## 精确目标

对每个满足 `Real.exp 3100 ≤ (N : ℝ)` 的奇自然数 `N`，证明它是三个奇素数之和，允许重复。
精确命题见 [`LiuWang/Target.lean`](LiuWang/Target.lean) 的 `LiuWang.TheoremStatement`。
该声明是 **`Prop` 的定义，不是该命题的证明或公理**。

这不是“所有不小于 9 的奇数”已经形式化完成的声明；阈值以下的范围还需要独立处理。

## 当前状态与阅读入口

- 已包含字符与零点计数、解析重数运输、筛法与显式公式、弧积分归约及若干严格有理证书。
- 条件性结果中的 Gamma、零点来源、密度估计和未付积分预算须继续逐项核对。
- 原论文的部分印式仍标为 `SOURCE_CHECK`；从其他已证等式推得的结果不表示该印式已被核实或修订。
- 源码没有因本次公开而改写数学定义或证明；内部工作树历史、运行日志、私有路径和中止稿不在此公开历史中。

详细边界见 [`docs/STATUS.md`](docs/STATUS.md)，源码入口见 [`docs/SOURCE_MAP.md`](docs/SOURCE_MAP.md)。
[`verification/status.json`](verification/status.json) 记录导出时的**部分本地检查进度**；不是全库验收证书或 GitHub CI 成功记录。

## 构建

固定工具链为 **Lean 4.33.0-rc1**。Mathlib 固定在 `lake-manifest.json` 中的 revision，保留该锁文件，不要先执行 `lake update` 更换依赖。
安装 [elan](https://github.com/leanprover/elan) 后，在仓库根目录：

```bash
lake exe cache get
lake build
```

上面是完整构建入口；**此公开版本尚不承诺完整构建已经通过**。首次准备依赖需要网络与足够磁盘空间，仓库不携带依赖缓存或编译对象。

仅检查精确目标定义（不能据此推断目标已证）：

```bash
env -u LEAN_PATH -u LEAN_SYSROOT lake env lean -DwarningAsError=true LiuWang/Target.lean
```

检查发布文件完整性，无需 Lean：

```bash
python3 scripts/check_source_inventory.py
```

## 逻辑基础与数学前提

Lean 的 `propext`、`Classical.choice`、`Quot.sound` 是标准逻辑基础，不能和未证明的数论输入混称为“假设主定理成立”。
另一方面，定理参数中的 Gamma 界、零密度估计等数学前提，即使不属于新声明的 `axiom`，也必须真正证明并接入，才可得到无条件结果。

## 原文与来源归属

主要路线：

- Ming-Chit Liu、Tianze Wang，*On the Vinogradov bound in the three primes Goldbach conjecture*，Acta Arithmetica **105.2** (2002)。
- Ming-Chit Liu、Tianze Wang，*Distribution of zeros of Dirichlet L-functions and an explicit formula for ψ(t, χ)*，Acta Arithmetica **102.3** (2002)。

复用了 [subfish-zhou/goldbach-lean](https://github.com/subfish-zhou/goldbach-lean) 中的选定基础，其中包含 **[UyNewNas/chen-theorem-lean](https://github.com/UyNewNas/chen-theorem-lean)**、[UyNewNas/analytic-number-theory-lean](https://github.com/UyNewNas/analytic-number-theory-lean) 等上游工作；还包含 Mathlib、PrimeNumberTheoremAnd、Bombieri–Vinogradov 与有限圆法相关来源的选定代码及兼容移植。
不将复用证明宣称为本项目原创。见 [`NOTICE`](NOTICE)、[`LICENSE`](LICENSE)、[`LICENSES/`](LICENSES/) 和 [`provenance/`](provenance/)。原文件作者及版权声明保留。

这是独立的公开源码仓库，不发布内部运行环境或完整内部 Git 历史。
