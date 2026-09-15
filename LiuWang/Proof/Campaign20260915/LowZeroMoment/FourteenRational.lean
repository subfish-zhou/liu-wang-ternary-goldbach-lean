import LiuWang.Proof.Campaign20260915.LowZeroMoment.FourteenBlock0
import LiuWang.Proof.Campaign20260915.LowZeroMoment.FourteenBlock1
import LiuWang.Proof.Campaign20260915.LowZeroMoment.FourteenBlock2
import LiuWang.Proof.Campaign20260915.LowZeroMoment.FourteenBlock3
import LiuWang.Proof.Campaign20260915.LowZeroMoment.FourteenBlock4
import LiuWang.Proof.Campaign20260915.LowZeroMoment.FourteenBlock5
import LiuWang.Proof.Campaign20260915.LowZeroMoment.FourteenBlock6
import LiuWang.Proof.Campaign20260915.LowZeroMoment.FourteenBlock7

set_option autoImplicit false

namespace LiuWang.Proof.Campaign20260915.LowZeroMoment
open LiuWang.Proof.Campaign20260915.ZetaValidation

def zeta14Center : QComplex :=
  ((∑ j ∈ Finset.range 64, (power14Center (j + 1)).1) -
      1041 / 1570 * (power14Center 64).1 + 3584 / 785 * (power14Center 64).2,
   (∑ j ∈ Finset.range 64, (power14Center (j + 1)).2) + zeta14TailIm)

theorem zeta14Center_im_blocks :
    zeta14Center.2 = (∑ b ∈ Finset.range 8, zeta14BlockIm b) + zeta14TailIm := by
  norm_num only [zeta14Center, zeta14BlockIm, Finset.sum_range_succ,
    Finset.sum_range_zero, Nat.reduceAdd, Nat.reduceMul]
  ring

set_option maxHeartbeats 1000000 in
theorem zeta14TailIm_upper : zeta14TailIm ≤ (143 / 1000 : ℚ) := by
  certify_zeta14_block

theorem zeta14Center_im_upper : zeta14Center.2 ≤ -(9 / 100 : ℚ) := by
  rw [zeta14Center_im_blocks]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero]
  linarith [zeta14Block0_upper, zeta14Block1_upper, zeta14Block2_upper,
    zeta14Block3_upper, zeta14Block4_upper, zeta14Block5_upper,
    zeta14Block6_upper, zeta14Block7_upper, zeta14TailIm_upper]

#print axioms zeta14Center_im_upper

end LiuWang.Proof.Campaign20260915.LowZeroMoment
