import LiuWang.Proof.ExceptionalZeroGap.LargeConductor

/-!
# 给定局部实零点：原常数距离界

`real_primitive_local_zero_gap` 在 `987 ≤ r ≤ x`、`10 ≤ x` 下，对实本原
字符和已经给定的 `β ≥ 1 - 1/(9.645908801 log x)` 实零点证明
`pi/(0.4923 sqrt r (log r)^2) ≤ 1-β`。

承重接口 `norm_deriv_LFunction_le` 是实际 `deriv χ.LFunction` 在该闭实段
上的范数界。有限头、单倍 Abel 尾、条件级数解析延拓、原数值常数及
全奇偶 `L(1)` 下界均已支付；`β<1` 由真实右半平面非零性推出。

`norm_deriv_LFunction_le_source_bound` 另导出原文完整头尾的指数形式，
对每个 `y≥10` 和所有 `σ≥nearOneLower x` 成立，无需 `σ≤1`。

不提供全族例外选择、零点存在/唯一/单根或小导子排除。
-/
