import LiuWang.Proof.VaughanKernelRows.Source

/-!
# 任意相位有理逼近核行界导出入口

`rational_phase_ball_card_le` 与 `rational_phase_kernel_le` 处理任意实相位。
`rational_row_nat_le`、`rational_row_le` 保留完整有限区间和实数差。
`source_row_bound` 保留取整余项，`source_row_le` 在原源域支付余项，
`source_row_le_logN` 再使用已证对数比较。

本入口不导出 S4 能量、行最大值或完整 Vaughan 指数和估计。
-/
