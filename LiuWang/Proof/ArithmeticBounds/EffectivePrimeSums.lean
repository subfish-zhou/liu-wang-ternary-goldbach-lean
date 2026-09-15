import LiuWang.Proof.ArithmeticBounds.ContinuationHelpers.SieveDensity
import LiuWang.Proof.ArithmeticBounds.ContinuationHelpers.IntervalMultiples
import LiuWang.Proof.Parameters.Main
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# 原文 §6 的全域有效 Möbius 矩

本文件支付 (6.20) 中实际的 `∑ |μ(t)| ≤ 0.6111 M`，不是
Rosser--Schoenfeld (4.5)，也不声称支付 (6.17) 的素数对数权或 (6.19)
的另一 Cauchy 因子。固定筛权给出全域线性余项 `272`，再在
`M ≥ 400000` 吸收；该范围包含原文的 `M ≥ exp(13.066)`。
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.ArithmeticBounds

open scoped BigOperators
open ContinuationHelpers

theorem sum_abs_moebius_dyadic_le_linear {M : Real} (hM : 0 ≤ M) :
    (∑ t ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊, |(ArithmeticFunction.moebius t : Real)|) ≤
      (30517 / 50000) * M + 272 := by
  calc
    _ ≤ ∑ t ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊,
        sieveForm (fun d => oddSquareIndicator d t) :=
      Finset.sum_le_sum fun t _ => abs_moebius_le_sieveForm t
    _ = sieveForm (fun d =>
        ∑ t ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊, oddSquareIndicator d t) :=
      sum_sieveForm _ _
    _ ≤ M * sieveForm oddDensity + 272 :=
      sieveForm_le (fun d hd => (dyadic_oddSquareIndicator_bounds hM d hd).1)
        (fun d hd => (dyadic_oddSquareIndicator_bounds hM d hd).2)
    _ ≤ (30517 / 50000) * M + 272 := by
      nlinarith [mul_le_mul_of_nonneg_left sieve_density_le hM]

/-- 左开右闭、实端点、全域的原系数 (6.20)。 -/
theorem sum_abs_moebius_dyadic_le_6111 {M : Real} (hM : 400000 ≤ M) :
    (∑ t ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊, |(ArithmeticFunction.moebius t : Real)|) ≤
      (6111 / 10000) * M := by
  have h := sum_abs_moebius_dyadic_le_linear (show 0 ≤ M by linarith)
  linarith

theorem fourHundredThousand_le_exp_13066 : (400000 : Real) ≤ Real.exp (6533 / 500) := by
  have he : (27 / 10 : Real) ≤ Real.exp 1 := by
    linarith [Real.exp_one_gt_d9]
  calc
    (400000 : Real) ≤ (27 / 10 : Real) ^ (13 : Nat) := by norm_num
    _ ≤ (Real.exp 1) ^ (13 : Nat) := pow_le_pow_left₀ (by norm_num) he _
    _ = Real.exp 13 := by rw [← Real.exp_nat_mul]; norm_num
    _ ≤ Real.exp (6533 / 500) := Real.exp_le_exp.mpr (by norm_num)

theorem sum_abs_moebius_dyadic_source_620 {M : Real}
    (hM : Real.exp (6533 / 500) ≤ M) :
    (∑ t ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊, |(ArithmeticFunction.moebius t : Real)|) ≤
      (6111 / 10000) * M :=
  sum_abs_moebius_dyadic_le_6111 (fourHundredThousand_le_exp_13066.trans hM)

theorem mem_moebius_dyadic_iff {M : Real} (hM : 0 ≤ M) {t : Nat} :
    t ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊ ↔ M < (t : Real) ∧ (t : Real) ≤ 2 * M := by
  rw [Finset.mem_Ioc, Nat.floor_lt hM, Nat.le_floor_iff (by positivity)]

theorem sourceVaughanV_ge_exp_13066 {N : Nat}
    (hN : Real.exp 2000 ≤ (N : Real)) :
    Real.exp (6533 / 500) ≤ Parameters.sourceVaughanV N := by
  apply (Real.le_log_iff_exp_le (Parameters.sourceVaughanV_pos hN)).mp
  rw [Parameters.log_sourceVaughanV hN]
  have hL := Parameters.sourceL_ge_2000 hN
  have hlog := Real.log_nonneg (Parameters.one_le_sourceL hN)
  linarith

/-- `j = 0` 对应原文 `M₁ = V`，不使用自然数截断减法来重编号。 -/
theorem sum_abs_moebius_sourceVaughan_block {N : Nat}
    (hN : Real.exp 2000 ≤ (N : Real)) (j : Nat) :
    (∑ t ∈ Finset.Ioc ⌊(2 : Real) ^ j * Parameters.sourceVaughanV N⌋₊
        ⌊2 * ((2 : Real) ^ j * Parameters.sourceVaughanV N)⌋₊,
      |(ArithmeticFunction.moebius t : Real)|) ≤
      (6111 / 10000) * ((2 : Real) ^ j * Parameters.sourceVaughanV N) := by
  apply sum_abs_moebius_dyadic_source_620
  exact (sourceVaughanV_ge_exp_13066 hN).trans
    (le_mul_of_one_le_left (Parameters.sourceVaughanV_pos hN).le
      (one_le_pow₀ (by norm_num : (1 : Real) ≤ 2)))

end LiuWang.Proof.ArithmeticBounds
