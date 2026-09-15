import LiuWang.Proof.VaughanTypeI.Decomposition
import LiuWang.Proof.VaughanTypeI.Estimates

/-!
# 原大 N 应用域的实际第一类包

闭窗口上 S1 消失，不使用 Chebyshev 或 Rosser--Schoenfeld 输入。
S2、S3 使用原系数；剩余项保持原实际 S4，不声明其估计。
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.VaughanTypeI

open Interfaces Parameters

theorem sourceVaughanU_lt_windowLower {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) :
    sourceVaughanU N < sourceWindowLower N := by
  have hlower : 0 < sourceWindowLower N := by
    exact div_pos (natCast_pos_of_exp_le hN) (by norm_num)
  apply (Real.log_lt_log_iff (sourceVaughanU_pos hN) hlower).mp
  rw [log_sourceVaughanU hN, sourceWindowLower,
    Real.log_div (natCast_pos_of_exp_le hN).ne' (by norm_num : (1000 : ℝ) ≠ 0)]
  change (2 * sourceL N - 4 * Real.log (sourceL N)) / 5 <
    sourceL N - Real.log 1000
  have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1000)
  have hL := sourceL_ge_2000 hN
  have hlogL := Real.log_nonneg (one_le_sourceL hN)
  linarith

theorem sourceLambda1_eq_zero_on_window {N n : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hn : n ∈ windowFinset N) :
    sourceLambda1 N n = 0 := by
  have hw := ((mem_windowFinset_iff N n).mp hn)
  have hl : sourceWindowLower N ≤ (n : ℝ) := by
    have h : (N : ℝ) ≤ 1000 * (n : ℝ) := by
      exact_mod_cast hw.2
    exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 1000)).mpr (by linarith)
  exact if_neg (not_le.mpr ((sourceVaughanU_lt_windowLower hN).trans_le hl))

theorem sourceS1_eq_zero {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (α : ℝ) : sourceS1 N α = 0 := by
  unfold sourceS1 windowSum
  apply Finset.sum_eq_zero
  intro n hn
  simp only [sourceLambda1_eq_zero_on_window hN hn, Complex.ofReal_zero, zero_mul]

theorem sourceS_eq_actual_remainder {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (α : ℝ) :
    S N α = sourceS2 N α + sourceS3 N α + sourceS4 N α := by
  have h2000 := exp_2000_le_of_exp_3100_le hN
  rw [sourceS_decomposition h2000, sourceS1_eq_zero h2000, zero_add]

theorem norm_sourceS_sub_actualS4_le_kernel {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (α : ℝ) :
    ‖S N α - sourceS4 N α‖ ≤
      sourceL N * ∑ t ∈ Finset.Icc 1 ⌊sourceVaughanV N⌋₊,
        truncatedKernel ((N : ℝ) / t) ((t : ℝ) * α) +
      Real.log (sourceVaughanU N * sourceVaughanV N) *
        ∑ d ∈ Finset.Icc 1 ⌊sourceVaughanU N * sourceVaughanV N⌋₊,
          truncatedKernel ((N : ℝ) / d) ((d : ℝ) * α) := by
  rw [sourceS_eq_actual_remainder hN, add_sub_cancel_right]
  exact (norm_add_le _ _).trans
    (add_le_add (norm_sourceS2_le_kernel (exp_2000_le_of_exp_3100_le hN) α)
      (norm_sourceS3_le_kernel (exp_2000_le_of_exp_3100_le hN) α))

theorem norm_sourceS_sub_actualS4_le {N a q : ℕ} {α θ : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hqL : sourceP1 N ≤ (q : ℝ)) (hqU : (q : ℝ) ≤ sourceQ N)
    (hi : sourceIndex a q) (hθ : |θ| ≤ 1)
    (hα : α = (a : ℝ) / q + θ / (q : ℝ) ^ 2) :
    ‖S N α - sourceS4 N α‖ ≤
      0.0413 * (N : ℝ) * (q : ℝ) ^ (-(1 / 2 : ℝ)) * sourceL N ^ 2 +
      0.8001 * (N : ℝ) ^ (4 / 5 : ℝ) * sourceL N ^ (7 / 5 : ℝ) +
      0.0011 * (N : ℝ) ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) *
        sourceL N ^ (5 / 2 : ℝ) := by
  rw [sourceS_eq_actual_remainder hN, add_sub_cancel_right]
  have h2 := sourceS2_bound hN hqL hqU hi hθ hα
  have h3 := sourceS3_bound hN hqL hqU hi hθ hα
  have hsum := norm_add_le (sourceS2 N α) (sourceS3 N α)
  nlinarith

theorem source_typeI_large {N a q : ℕ} {α θ : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hqL : sourceP1 N ≤ (q : ℝ)) (hqU : (q : ℝ) ≤ sourceQ N)
    (hi : sourceIndex a q) (hθ : |θ| ≤ 1)
    (hα : α = (a : ℝ) / q + θ / (q : ℝ) ^ 2) :
    S N α = sourceS1 N α + sourceS2 N α + sourceS3 N α + sourceS4 N α ∧
    sourceS1 N α = 0 ∧
    ‖sourceS2 N α‖ ≤
      0.0282 * (N : ℝ) * (q : ℝ) ^ (-(1 / 2 : ℝ)) * sourceL N ^ 2 +
      0.0001 * (N : ℝ) ^ (4 / 5 : ℝ) * sourceL N ^ (7 / 5 : ℝ) +
      0.0006 * (N : ℝ) ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) *
        sourceL N ^ (5 / 2 : ℝ) ∧
    ‖sourceS3 N α‖ ≤
      0.0131 * (N : ℝ) * (q : ℝ) ^ (-(1 / 2 : ℝ)) * sourceL N ^ 2 +
      0.8 * (N : ℝ) ^ (4 / 5 : ℝ) * sourceL N ^ (7 / 5 : ℝ) +
      0.0005 * (N : ℝ) ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) *
        sourceL N ^ (5 / 2 : ℝ) ∧
    ‖S N α - sourceS4 N α‖ ≤
      0.0413 * (N : ℝ) * (q : ℝ) ^ (-(1 / 2 : ℝ)) * sourceL N ^ 2 +
      0.8001 * (N : ℝ) ^ (4 / 5 : ℝ) * sourceL N ^ (7 / 5 : ℝ) +
      0.0011 * (N : ℝ) ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) *
        sourceL N ^ (5 / 2 : ℝ) :=
  ⟨sourceS_decomposition (exp_2000_le_of_exp_3100_le hN) α,
    sourceS1_eq_zero (exp_2000_le_of_exp_3100_le hN) α,
    sourceS2_bound hN hqL hqU hi hθ hα, sourceS3_bound hN hqL hqU hi hθ hα,
    norm_sourceS_sub_actualS4_le hN hqL hqU hi hθ hα⟩

end LiuWang.Proof.VaughanTypeI
