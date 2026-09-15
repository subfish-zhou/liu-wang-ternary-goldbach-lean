import LiuWang.Proof.ArithmeticBounds.LambdaMoment.Main

/-! 消费真实 `sourceLargeDivisorWeight`，不以抽象 W 或尾界假设替代。
内层系数矩的子集界也保留原 `sourceVaughanInnerSupport`；指数和本身仍未闭合。 -/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.ArithmeticBounds.LambdaMoment

open scoped BigOperators
open Parameters

theorem source_actual_moment {N : Nat} {M : Real}
    (hN : Real.exp 3100 ≤ (N : Real))
    (hM : sourceVaughanV N ≤ M) (hM' : M ≤ (N : Real) / sourceVaughanU N) :
    (∑ m ∈ Finset.Ioc ⌊sourceVaughanU N⌋₊ ⌊(N : Real) / M⌋₊,
      sourceLargeDivisorWeight N m ^ 2) ≤
        ((N : Real) / M) * (W1 N ((N : Real) / M) + 25876 / 10000 +
          2 * (681 / 10000)) :=
  actualMoment_source_high_powers_paid hN hM hM'

theorem source_inner_support_subset {N t : Nat} {M : Real}
    (hN : Real.exp 3100 ≤ (N : Real))
    (hM : sourceVaughanV N ≤ M) (ht : M ≤ (t : Real)) :
    sourceVaughanInnerSupport N t ⊆ momentSupport N ((N : Real) / M) := by
  have hn := exp_2000_le_of_exp_3100_le hN
  have hM0 := (sourceVaughanV_pos hn).trans_le hM
  have hX0 : 0 ≤ (N : Real) / M := div_nonneg (Nat.cast_nonneg N) hM0.le
  intro m hm
  have hm' := (mem_sourceVaughanInnerSupport_iff N t m).1 hm
  exact (mem_momentSupport hn hX0).2 ⟨hm'.2,
    hm'.1.2.trans (div_le_div_of_nonneg_left (Nat.cast_nonneg N) hM0 ht)⟩

theorem source_inner_weight_moment {N t : Nat} {M : Real}
    (hN : Real.exp 3100 ≤ (N : Real))
    (hM : sourceVaughanV N ≤ M) (hM' : M ≤ (N : Real) / sourceVaughanU N)
    (ht : M ≤ (t : Real)) :
    (∑ m ∈ sourceVaughanInnerSupport N t, sourceLargeDivisorWeight N m ^ 2) ≤
      ((N : Real) / M) * (W1 N ((N : Real) / M) + 25876 / 10000 +
        2 * (681 / 10000)) := by
  apply le_trans _ (actualMoment_source_high_powers_paid hN hM hM')
  exact Finset.sum_le_sum_of_subset_of_nonneg (source_inner_support_subset hN hM ht)
    (fun m _ _ => sq_nonneg _)

theorem source_dyadic_actual_moment {N : Nat}
    (hN : Real.exp 3100 ≤ (N : Real)) (j : Nat)
    (hj : (2 : Real) ^ j * sourceVaughanV N ≤ (N : Real) / sourceVaughanU N) :
    (∑ m ∈ Finset.Ioc ⌊sourceVaughanU N⌋₊
      ⌊(N : Real) / ((2 : Real) ^ j * sourceVaughanV N)⌋₊,
      sourceLargeDivisorWeight N m ^ 2) ≤
        ((N : Real) / ((2 : Real) ^ j * sourceVaughanV N)) *
          (W1 N ((N : Real) / ((2 : Real) ^ j * sourceVaughanV N)) +
            25876 / 10000 + 2 * (681 / 10000)) := by
  apply source_actual_moment hN _ hj
  exact le_mul_of_one_le_left
    (sourceVaughanV_pos (exp_2000_le_of_exp_3100_le hN)).le
    (one_le_pow₀ (by norm_num))

end LiuWang.Proof.ArithmeticBounds.LambdaMoment
