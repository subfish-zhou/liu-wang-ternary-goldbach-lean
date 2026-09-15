import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.Block0
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.Block1
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.Block2
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.Block3
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.Block4
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.Block5
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.Block6
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.Block7

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281

def fixedBlockSum (j : ℕ) : ℝ :=
  ∑ k ∈ Finset.range 32, fixedCellUpper (j * 32 + k)

theorem sum_fixed_blocks (n : ℕ) :
    (∑ i ∈ Finset.range (n * 32), fixedCellUpper i) =
      ∑ j ∈ Finset.range n, fixedBlockSum j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ (f := fixedBlockSum)]
    rfl

theorem fixed_rational_budget :
    (8 * 6.76661 * (1.7810725 * 3.182937 + 2.50637 / 3.182936) * 3100) *
      (∑ i ∈ Finset.range 256, fixedCellUpper i) ≤
      (128436926173372598287618471972397118913709 : ℝ) /
        3978670000000000000000000000000000000000000 := by
  rw [show 256 = 8 * 32 by norm_num, sum_fixed_blocks]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp only [fixedBlockSum, Nat.reduceMul, zero_add]
  have h := add_le_add
    (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
      block_0 block_1) block_2) block_3) block_4) block_5) block_6) block_7
  have hm := mul_le_mul_of_nonneg_left h (by norm_num :
    (0 : ℝ) ≤ 8 * 6.76661 * (1.7810725 * 3.182937 + 2.50637 / 3.182936) * 3100)
  norm_num at hm
  linarith only [hm]

theorem original_fixed_256_budget :
    originalDensityScalar 3100 ≤
      (128436926173372598287618471972397118913709 : ℝ) /
        3978670000000000000000000000000000000000000 :=
  fixed_rational_reduction.trans fixed_rational_budget

theorem candidate_256_above_target :
    (32281 : ℝ) / 1000000 <
      (128436926173372598287618471972397118913709 : ℝ) /
        3978670000000000000000000000000000000000000 := by norm_num

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281
