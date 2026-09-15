import LiuWang.Proof.ArithmeticBounds.Continuation

/-!
# (6.20) 在 Vaughan 分块 Cauchy 界中的实际消费

保留带符号的 Möbius 系数和任意复数内层和，支付 (6.11) 的第一个因子。
第二个因子仍是实际平方范数和，不假定 (6.19) 的未证估计。
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.ArithmeticBounds

open scoped BigOperators

theorem abs_moebius_sq (n : Nat) :
    |(ArithmeticFunction.moebius n : Real)| ^ 2 = |(ArithmeticFunction.moebius n : Real)| := by
  by_cases hn : Squarefree n
  · have hm : |(ArithmeticFunction.moebius n : Real)| = 1 := by
      rw [← Int.cast_abs, ArithmeticFunction.abs_moebius_eq_one_of_squarefree hn]
      norm_num
    rw [hm]
    norm_num
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn]
    norm_num

theorem moebius_weighted_cauchy (s : Finset Nat) (c : Nat → Complex) :
    ‖∑ t ∈ s, (ArithmeticFunction.moebius t : Real) • c t‖ ^ 2 ≤
      (∑ t ∈ s, |(ArithmeticFunction.moebius t : Real)|) *
        (∑ t ∈ s, ‖c t‖ ^ 2) := by
  have hnorm : ‖∑ t ∈ s, (ArithmeticFunction.moebius t : Real) • c t‖ ≤
      ∑ t ∈ s, |(ArithmeticFunction.moebius t : Real)| * ‖c t‖ := by
    calc
      _ ≤ ∑ t ∈ s, ‖(ArithmeticFunction.moebius t : Real) • c t‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_smul, Real.norm_eq_abs]
  have hC := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun t => |(ArithmeticFunction.moebius t : Real)|) (fun t => ‖c t‖)
  simp only [abs_moebius_sq] at hC
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans hC

theorem moebius_dyadic_cauchy_6111 {M : Real} (hM : 400000 ≤ M)
    (c : Nat → Complex) :
    ‖∑ t ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊,
        (ArithmeticFunction.moebius t : Real) • c t‖ ^ 2 ≤
      (6111 / 10000) * M * (∑ t ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊, ‖c t‖ ^ 2) := by
  exact (moebius_weighted_cauchy _ c).trans
    (mul_le_mul_of_nonneg_right (sum_abs_moebius_dyadic_le_6111 hM)
      (Finset.sum_nonneg fun t _ => sq_nonneg ‖c t‖))

theorem sourceVaughan_block_cauchy {N : Nat}
    (hN : Real.exp 3100 ≤ (N : Real)) (j : Nat) (c : Nat → Complex) :
    ‖∑ t ∈ Finset.Ioc ⌊(2 : Real) ^ j * Parameters.sourceVaughanV N⌋₊
        ⌊2 * ((2 : Real) ^ j * Parameters.sourceVaughanV N)⌋₊,
      (ArithmeticFunction.moebius t : Real) • c t‖ ^ 2 ≤
      (6111 / 10000) * ((2 : Real) ^ j * Parameters.sourceVaughanV N) *
        (∑ t ∈ Finset.Ioc ⌊(2 : Real) ^ j * Parameters.sourceVaughanV N⌋₊
          ⌊2 * ((2 : Real) ^ j * Parameters.sourceVaughanV N)⌋₊, ‖c t‖ ^ 2) := by
  exact (moebius_weighted_cauchy _ c).trans
    (mul_le_mul_of_nonneg_right
      (sum_abs_moebius_sourceVaughan_block (Parameters.exp_2000_le_of_exp_3100_le hN) j)
      (Finset.sum_nonneg fun t _ => sq_nonneg ‖c t‖))

/-- 原文 (6.10) 的 `a_m`，保留所有素数幂的 von Mangoldt 权。 -/
def sourceLargeDivisorWeight (N m : Nat) : Real :=
  ∑ r ∈ m.divisors.filter (fun r : Nat => Parameters.sourceVaughanU N < (r : Real)),
    ArithmeticFunction.vonMangoldt r

/-- 此处严格采用 (6.11) 显示的左开端点，不声称已证明完整 Vaughan 分解。 -/
def sourceVaughanInnerSupport (N t : Nat) : Finset Nat :=
  (Finset.Ioc ⌊Interfaces.sourceWindowLower N / (t : Real)⌋₊
    ⌊(N : Real) / (t : Real)⌋₊).filter
      (fun m => Parameters.sourceVaughanU N < (m : Real))

theorem mem_sourceVaughanInnerSupport_iff (N t m : Nat) :
    m ∈ sourceVaughanInnerSupport N t ↔
      (Interfaces.sourceWindowLower N / (t : Real) < (m : Real) ∧
        (m : Real) ≤ (N : Real) / (t : Real)) ∧
      Parameters.sourceVaughanU N < (m : Real) := by
  have hl : 0 ≤ Interfaces.sourceWindowLower N / (t : Real) := by
    unfold Interfaces.sourceWindowLower
    positivity
  have hu : 0 ≤ (N : Real) / (t : Real) := by positivity
  simp only [sourceVaughanInnerSupport, Finset.mem_filter, Finset.mem_Ioc,
    Nat.floor_lt hl, Nat.le_floor_iff hu]

def sourceVaughanInnerSum (N t : Nat) (α : Real) : Complex :=
  ∑ m ∈ sourceVaughanInnerSupport N t,
    (sourceLargeDivisorWeight N m : Complex) *
      AnalyticNumberTheory.LargeSieve.charReal (α * (m : Real) * (t : Real))

theorem sourceVaughan_actual_inner_cauchy {N : Nat}
    (hN : Real.exp 3100 ≤ (N : Real)) (j : Nat) (α : Real) :
    ‖∑ t ∈ Finset.Ioc ⌊(2 : Real) ^ j * Parameters.sourceVaughanV N⌋₊
        ⌊2 * ((2 : Real) ^ j * Parameters.sourceVaughanV N)⌋₊,
      (ArithmeticFunction.moebius t : Real) • sourceVaughanInnerSum N t α‖ ^ 2 ≤
      (6111 / 10000) * ((2 : Real) ^ j * Parameters.sourceVaughanV N) *
        (∑ t ∈ Finset.Ioc ⌊(2 : Real) ^ j * Parameters.sourceVaughanV N⌋₊
          ⌊2 * ((2 : Real) ^ j * Parameters.sourceVaughanV N)⌋₊,
            ‖sourceVaughanInnerSum N t α‖ ^ 2) :=
  sourceVaughan_block_cauchy hN j (fun t => sourceVaughanInnerSum N t α)

end LiuWang.Proof.ArithmeticBounds
