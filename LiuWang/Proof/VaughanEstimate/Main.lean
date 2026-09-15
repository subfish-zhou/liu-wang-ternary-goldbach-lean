import LiuWang.Proof.VaughanKernelRows.Consumer
import LiuWang.Proof.VaughanTypeIIBudget.Consumer
import LiuWang.Proof.VaughanTypeIIBudget.KernelBridge

/-!
# 原闭窗口上的完整 Vaughan 估计

实际任意相位行界先约束有限行最大值，再消费真实二进能量和已付标量预算。
同一个有理逼近用于全部行、第一类和第二类；没有未付行界前提。
保留较强三项系数，并提供原系数及全分母区间的数值推论。
-/

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.VaughanEstimate

open Interfaces Parameters VaughanTypeII VaughanTypeIIBudget

theorem rowSum_le_scalarRowBudget {N a q : ℕ} {α θ M : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hqL : sourceP1 N ≤ (q : ℝ))
    (hi : sourceIndex a q) (hθ : |θ| ≤ 1)
    (hα : α = (a : ℝ) / q + θ / (q : ℝ) ^ 2)
    (hVM : sourceVaughanV N ≤ M) (hMU : M ≤ (N : ℝ) / sourceVaughanU N)
    (m : ℕ) : rowSum N M α m ≤ scalarRowBudget N M q := by
  simpa only [rowSum, coefficientSupport, kernel_eq_truncatedKernel, scalarRowBudget] using
    VaughanKernelRows.source_row_le hN hqL hi.2.2 hθ hα hVM hMU m

theorem rowMax_le_scalarRowBudget {N a q : ℕ} {α θ M : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hqL : sourceP1 N ≤ (q : ℝ))
    (hi : sourceIndex a q) (hθ : |θ| ≤ 1)
    (hα : α = (a : ℝ) / q + θ / (q : ℝ) ^ 2)
    (hVM : sourceVaughanV N ≤ M) (hMU : M ≤ (N : ℝ) / sourceVaughanU N) :
    rowMax N M α ≤ scalarRowBudget N M q := by
  classical
  unfold rowMax
  apply Finset.max'_le
  intro y hy
  rcases Finset.mem_insert.mp hy with rfl | hy
  · have hM := (sourceVaughanV_pos (exp_2000_le_of_exp_3100_le hN)).le.trans hVM
    have hq : 1 ≤ (q : ℝ) := by exact_mod_cast (hi.1.trans hi.2.1)
    exact scalarRowBudget_nonneg hM hq
  · rcases Finset.mem_image.mp hy with ⟨m, _, rfl⟩
    exact rowSum_le_scalarRowBudget hN hqL hi hθ hα hVM hMU m

theorem dyadic_rowMax_le_scalarRowBudget {N a q : ℕ} {α θ : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hqL : sourceP1 N ≤ (q : ℝ))
    (hi : sourceIndex a q) (hθ : |θ| ≤ 1)
    (hα : α = (a : ℝ) / q + θ / (q : ℝ) ^ 2) :
    ∀ j < dyadicCount N,
      rowMax N (dyadicScale N j) α ≤ scalarRowBudget N (dyadicScale N j) q := by
  intro j hj
  have hn := exp_2000_le_of_exp_3100_le hN
  exact rowMax_le_scalarRowBudget hN hqL hi hθ hα
    (V_le_dyadicScale hn j) (dyadicScale_lt_upper hn hj).le

theorem norm_sourceS4_le {N a q : ℕ} {α θ : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hqL : sourceP1 N ≤ (q : ℝ)) (hqU : (q : ℝ) ≤ sourceQ N)
    (hi : sourceIndex a q) (hθ : |θ| ≤ 1)
    (hα : α = (a : ℝ) / q + θ / (q : ℝ) ^ 2) :
    ‖VaughanTypeI.sourceS4 N α‖ ≤
      0.1526 * termA N q + 2.5179 * termB N + 0.0872 * termC N q :=
  conditional_actual_typeII_le hN hqL hqU
    (dyadic_rowMax_le_scalarRowBudget hN hqL hi hθ hα)

theorem norm_sourceS_le_strong {N a q : ℕ} {α θ : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hqL : sourceP1 N ≤ (q : ℝ)) (hqU : (q : ℝ) ≤ sourceQ N)
    (hi : sourceIndex a q) (hθ : |θ| ≤ 1)
    (hα : α = (a : ℝ) / q + θ / (q : ℝ) ^ 2) :
    ‖S N α‖ ≤ 0.1939 * termA N q + 3.318 * termB N + 0.0883 * termC N q :=
  conditional_sourceS_le_strong hN hqL hqU hi hθ hα
    (dyadic_rowMax_le_scalarRowBudget hN hqL hi hθ hα)

theorem norm_sourceS_le_vaughan {N a q : ℕ} {α θ : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hqL : sourceP1 N ≤ (q : ℝ)) (hqU : (q : ℝ) ≤ sourceQ N)
    (hi : sourceIndex a q) (hθ : |θ| ≤ 1)
    (hα : α = (a : ℝ) / q + θ / (q : ℝ) ^ 2) :
    ‖S N α‖ ≤
      (0.28 : ℝ) * (N : ℝ) * (q : ℝ) ^ ((-1 : ℝ) / 2) * sourceL N ^ (2 : ℕ) +
      4 * (N : ℝ) ^ ((4 : ℝ) / 5) * sourceL N ^ ((7 : ℝ) / 5) +
      (0.09 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 2) * (q : ℝ) ^ ((1 : ℝ) / 2) *
        sourceL N ^ ((5 : ℝ) / 2) :=
  conditional_sourceS_le_vaughan hN hqL hqU hi hθ hα
    (dyadic_rowMax_le_scalarRowBudget hN hqL hi hθ hα)

theorem norm_sourceS_le_margin {N a q : ℕ} {α θ : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hqL : sourceP1 N ≤ (q : ℝ)) (hqU : (q : ℝ) ≤ sourceQ N)
    (hi : sourceIndex a q) (hθ : |θ| ≤ 1)
    (hα : α = (a : ℝ) / q + θ / (q : ℝ) ^ 2) :
    ‖S N α‖ ≤ (0.294 : ℝ) * (N : ℝ) / sourceL N :=
  conditional_sourceS_le_margin hN hqL hqU hi hθ hα
    (dyadic_rowMax_le_scalarRowBudget hN hqL hi hθ hα)

theorem norm_sourceS_le_three_tenths {N a q : ℕ} {α θ : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hqL : sourceP1 N ≤ (q : ℝ)) (hqU : (q : ℝ) ≤ sourceQ N)
    (hi : sourceIndex a q) (hθ : |θ| ≤ 1)
    (hα : α = (a : ℝ) / q + θ / (q : ℝ) ^ 2) :
    ‖S N α‖ ≤ (0.3 : ℝ) * (N : ℝ) / sourceL N :=
  conditional_sourceS_le_three_tenths hN hqL hqU hi hθ hα
    (dyadic_rowMax_le_scalarRowBudget hN hqL hi hθ hα)

end LiuWang.Proof.VaughanEstimate
