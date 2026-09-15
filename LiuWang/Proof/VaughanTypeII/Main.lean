import LiuWang.Proof.VaughanTypeII.Geometric

/-!
# 实际第二类有限和的无条件接口

`rowMax` 是插入零后的有限行最大值，包含共振项；本模块没有 q 或有理逼近假设。
0.31 与 0.6111 都来自冻结的算术生产者。未来核计数只需估计这个实际 `rowMax`。
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.VaughanTypeII

open Finset Interfaces Parameters ArithmeticBounds
open scoped BigOperators

theorem actual_typeII_bound {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (α : ℝ) :
    ‖VaughanTypeI.sourceS4 N α‖ ≤
      Real.sqrt ((6111 / 10000) * (31 / 100)) * Real.sqrt (N : ℝ) *
        Real.log ((N : ℝ) / sourceVaughanV N) *
          ∑ j ∈ range (dyadicCount N), Real.sqrt (rowMax N (dyadicScale N j) α) := by
  have hn := exp_2000_le_of_exp_3100_le hN
  have hlog : 0 ≤ Real.log ((N : ℝ) / sourceVaughanV N) :=
    Real.log_nonneg ((one_le_div (sourceVaughanV_pos hn)).mpr
      (sourceVaughanV_lt_natCast hn).le)
  refine (sourceS4_le_sqrt_sum hN α).trans_eq ?_
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  rw [Real.sqrt_mul (by positivity :
    0 ≤ ((6111 / 10000) * (31 / 100)) * (N : ℝ) *
      Real.log ((N : ℝ) / sourceVaughanV N) ^ 2),
    Real.sqrt_mul (by positivity : 0 ≤ ((6111 / 10000) * (31 / 100)) * (N : ℝ)),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ (6111 / 10000) * (31 / 100)),
    Real.sqrt_sq hlog]

theorem commonSupport_eq_actual_support {N m m' : ℕ} {M : ℝ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hM : sourceVaughanV N ≤ M)
    (hm : m ∈ coefficientSupport N M) (hm' : m' ∈ coefficientSupport N M) :
    commonSupport N M m m' =
      (blockSupport M).filter fun t => m ∈ closedSupport N t ∧ m' ∈ closedSupport N t := by
  obtain ⟨hmI, hmU⟩ := coefficientSupport_geometry hN hM hm
  obtain ⟨hm'I, hm'U⟩ := coefficientSupport_geometry hN hM hm'
  ext t
  simp only [commonSupport, closedSupport, mem_filter, hmI, hmU, hm'I, hm'U, true_and]

theorem closedSupport_includes_lower_endpoint {N m t : ℕ}
    (hm : m ∈ Icc 1 N) (hU : sourceVaughanU N < (m : ℝ))
    (hend : N = 1000 * (m * t)) : m ∈ closedSupport N t := by
  apply mem_filter.mpr
  refine ⟨hm, hU, ?_⟩
  simp only [mem_windowFinset_iff, mem_windowSet_iff]
  constructor <;> omega

end LiuWang.Proof.VaughanTypeII
