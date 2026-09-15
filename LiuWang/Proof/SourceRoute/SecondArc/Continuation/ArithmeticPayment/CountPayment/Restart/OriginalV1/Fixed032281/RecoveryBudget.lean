import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.Refined0
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.RecoveryGroup01
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.RecoveryGroup02
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.RecoveryGroup03
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.RecoveryGroup04
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.RecoveryGroup05
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.RecoveryGroup06
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.RecoveryGroup07
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.RecoveryGroup08
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.RecoveryGroup09
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.RecoveryGroup10
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.RecoveryGroup11
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.RecoveryGroup12
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.RecoveryGroup13
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.RecoveryGroup14
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.RecoveryGroup15

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281

def recoveryBlockSum (j : ℕ) : ℝ :=
  ∑ k ∈ Finset.range 64, refinedCellUpper (j * 64 + k)

theorem recovery_blocks_cover (n : ℕ) :
    (∑ i ∈ Finset.range (n * 64), refinedCellUpper i) =
      ∑ j ∈ Finset.range n, recoveryBlockSum j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ (f := recoveryBlockSum)]
    rfl

theorem recovery_rational_budget :
    (8 * 6.76661 * (1.7810725 * 3.182937 + 2.50637 / 3.182936) * 3100) *
      (∑ i ∈ Finset.range 1024, refinedCellUpper i) ≤ (32281 : ℝ) / 1000000 := by
  rw [show 1024 = 16 * 64 by norm_num, recovery_blocks_cover]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp only [recoveryBlockSum, Nat.reduceMul, zero_add]
  have h := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
      (add_le_add (add_le_add (add_le_add refined_block_0 recovery_group01)
        recovery_group02) recovery_group03) recovery_group04) recovery_group05)
          recovery_group06) recovery_group07) recovery_group08) recovery_group09)
            recovery_group10) recovery_group11) recovery_group12) recovery_group13)
              recovery_group14) recovery_group15
  have hm := mul_le_mul_of_nonneg_left h (by norm_num :
    (0 : ℝ) ≤ 8 * 6.76661 * (1.7810725 * 3.182937 + 2.50637 / 3.182936) * 3100)
  norm_num at hm
  linarith only [hm]

theorem original_fixed_032281 :
    originalDensityScalar 3100 ≤ (32281 : ℝ) / 1000000 :=
  refined_rational_reduction.trans recovery_rational_budget

theorem original_all_L_032281 (L : ℝ) (hL : 3100 ≤ L) :
    originalDensityScalar L ≤ (32281 : ℝ) / 1000000 :=
  (originalDensityScalar_le_base hL).trans original_fixed_032281

#check recoveryBlockSum
#print axioms recoveryBlockSum
#check recovery_blocks_cover
#print axioms recovery_blocks_cover
#check recovery_rational_budget
#print axioms recovery_rational_budget
#check original_fixed_032281
#print axioms original_fixed_032281
#check original_all_L_032281
#print axioms original_all_L_032281

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281
