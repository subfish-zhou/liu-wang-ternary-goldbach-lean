import LiuWang.Proof.ArithmeticBounds.PrimeMoment.Budget

/-!
# 实际 Vaughan 系数的 0.31 平方矩预算

在整个 `N ≥ exp 3100`、`V ≤ M ≤ N/U` 域支付真实 W1，并保留已付高幂常数
`2043/10000`。此结论不声称已闭合 Vaughan 指数和，也不修改最终指数和常数。
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.ArithmeticBounds.PrimeMoment

open Parameters LambdaMoment

theorem actualMoment_source_le_31 {N : Nat} {M : Real}
    (hN : Real.exp 3100 ≤ (N : Real))
    (hM : sourceVaughanV N ≤ M) (hM' : M ≤ (N : Real) / sourceVaughanU N) :
    actualMoment N ((N : Real) / M) ≤
      (31 / 100) * ((N : Real) / M) *
        Real.log ((N : Real) / sourceVaughanV N) ^ 2 := by
  have hg := source_quotient_geometry hN hM hM'
  calc
    _ ≤ ((N : Real) / M) * (W1 N ((N : Real) / M) + 2043 / 10000) :=
      actualMoment_source_high_powers_sharp hN hM hM'
    _ ≤ ((N : Real) / M) *
        ((31 / 100) * Real.log ((N : Real) / sourceVaughanV N) ^ 2) :=
      mul_le_mul_of_nonneg_left (source_prime_budget_31 hN hM hM')
        (div_nonneg (Nat.cast_nonneg N) hg.1.le)
    _ = _ := by ring

end LiuWang.Proof.ArithmeticBounds.PrimeMoment
