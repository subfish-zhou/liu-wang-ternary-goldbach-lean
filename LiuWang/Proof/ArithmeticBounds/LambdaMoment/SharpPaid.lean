import LiuWang.Proof.ArithmeticBounds.LambdaMoment.Consumer

/-! 保留已证的更好高幂常数，直接接到同一实际矩及内层支持。
没有证明剩余素数和 W1 的预算，也不声称指数和已闭合。 -/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.ArithmeticBounds.LambdaMoment

open scoped BigOperators
open Parameters

theorem actualMoment_source_high_powers_sharp {N : Nat} {M : Real}
    (hN : Real.exp 3100 ≤ (N : Real))
    (hM : sourceVaughanV N ≤ M) (hM' : M ≤ (N : Real) / sourceVaughanU N) :
    actualMoment N ((N : Real) / M) ≤
      ((N : Real) / M) * (W1 N ((N : Real) / M) + 2043 / 10000) := by
  have hg := source_quotient_geometry hN hM hM'
  have h2 : W2 N ((N : Real) / M) ≤ 681 / 10000 := W2_le_681 hN
  have h3 : W3 N ((N : Real) / M) ≤ 681 / 10000 := W3_le_681 hN
  apply (actualMoment_source_le_613 hN hM hM').trans
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (Nat.cast_nonneg N) hg.1.le)
  linarith

theorem source_inner_weight_moment_sharp {N t : Nat} {M : Real}
    (hN : Real.exp 3100 ≤ (N : Real))
    (hM : sourceVaughanV N ≤ M) (hM' : M ≤ (N : Real) / sourceVaughanU N)
    (ht : M ≤ (t : Real)) :
    (∑ m ∈ sourceVaughanInnerSupport N t, sourceLargeDivisorWeight N m ^ 2) ≤
      ((N : Real) / M) * (W1 N ((N : Real) / M) + 2043 / 10000) := by
  apply le_trans _ (actualMoment_source_high_powers_sharp hN hM hM')
  exact Finset.sum_le_sum_of_subset_of_nonneg (source_inner_support_subset hN hM ht)
    (fun m _ _ => sq_nonneg _)

end LiuWang.Proof.ArithmeticBounds.LambdaMoment
