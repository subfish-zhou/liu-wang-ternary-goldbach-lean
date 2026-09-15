import LiuWang.Proof.ArithmeticBounds.PrimeMoment.Main

/-! 同一 M 下的实际平方和及原内层支持消费者，不替换系数、端点或同底重数。 -/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.ArithmeticBounds.PrimeMoment

open scoped BigOperators
open Parameters LambdaMoment

theorem source_actual_moment_31 {N : Nat} {M : Real}
    (hN : Real.exp 3100 ≤ (N : Real))
    (hM : sourceVaughanV N ≤ M) (hM' : M ≤ (N : Real) / sourceVaughanU N) :
    (∑ m ∈ Finset.Ioc ⌊sourceVaughanU N⌋₊ ⌊(N : Real) / M⌋₊,
      sourceLargeDivisorWeight N m ^ 2) ≤
        (31 / 100) * ((N : Real) / M) *
          Real.log ((N : Real) / sourceVaughanV N) ^ 2 :=
  actualMoment_source_le_31 hN hM hM'

theorem source_inner_weight_moment_31 {N t : Nat} {M : Real}
    (hN : Real.exp 3100 ≤ (N : Real))
    (hM : sourceVaughanV N ≤ M) (hM' : M ≤ (N : Real) / sourceVaughanU N)
    (ht : M ≤ (t : Real)) :
    (∑ m ∈ sourceVaughanInnerSupport N t, sourceLargeDivisorWeight N m ^ 2) ≤
      (31 / 100) * ((N : Real) / M) *
        Real.log ((N : Real) / sourceVaughanV N) ^ 2 := by
  have hg := source_quotient_geometry hN hM hM'
  calc
    _ ≤ ((N : Real) / M) * (W1 N ((N : Real) / M) + 2043 / 10000) :=
      source_inner_weight_moment_sharp hN hM hM' ht
    _ ≤ ((N : Real) / M) *
        ((31 / 100) * Real.log ((N : Real) / sourceVaughanV N) ^ 2) :=
      mul_le_mul_of_nonneg_left (source_prime_budget_31 hN hM hM')
        (div_nonneg (Nat.cast_nonneg N) hg.1.le)
    _ = _ := by ring

theorem source_dyadic_actual_moment_31 {N : Nat}
    (hN : Real.exp 3100 ≤ (N : Real)) (j : Nat)
    (hj : (2 : Real) ^ j * sourceVaughanV N ≤ (N : Real) / sourceVaughanU N) :
    (∑ m ∈ Finset.Ioc ⌊sourceVaughanU N⌋₊
      ⌊(N : Real) / ((2 : Real) ^ j * sourceVaughanV N)⌋₊,
      sourceLargeDivisorWeight N m ^ 2) ≤
        (31 / 100) * ((N : Real) / ((2 : Real) ^ j * sourceVaughanV N)) *
          Real.log ((N : Real) / sourceVaughanV N) ^ 2 := by
  apply source_actual_moment_31 hN _ hj
  exact le_mul_of_one_le_left
    (sourceVaughanV_pos (exp_2000_le_of_exp_3100_le hN)).le
    (one_le_pow₀ (by norm_num))

end LiuWang.Proof.ArithmeticBounds.PrimeMoment
