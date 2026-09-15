import LiuWang.Proof.Campaign20260915.LowZeroMoment.FourteenMomentBound

/-! Actual global lower zero height and its all-order moment consumer.
This is not a numerical proof of the first three inverse moments.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open BombieriVinogradov.SiegelWalfisz
namespace LiuWang.Proof.Campaign20260915.Parent.FourteenMomentAudit
open LiuWang.Proof.Campaign20260915.LowZeroMoment

theorem actual_zero_height {s : ℂ}
    (hz : riemannZeta s = 0) (h0 : 0 < s.re) (h1 : s.re < 1) :
    14 < |s.im| :=
  zeta_zero_height_gt_fourteen hz h0 h1

theorem actual_higher_moment {m : ℕ} (hm : 3 ≤ m) :
    (∑' p : RiemannXiDivisorZeroIndex,
      1 / |(riemannXiDivisorZeroValue p).im| ^ (m + 1)) ≤
      (14 : ℝ) ^ (3 - (m : ℝ)) *
        ∑' p : RiemannXiDivisorZeroIndex,
          1 / |(riemannXiDivisorZeroValue p).im| ^ 4 :=
  xi_height_moment_le_third hm

#print axioms actual_zero_height
#print axioms actual_higher_moment
end LiuWang.Proof.Campaign20260915.Parent.FourteenMomentAudit

#print axioms LiuWang.Proof.Campaign20260915.LowZeroMoment.abelApprox_fourteen_formula
#print axioms LiuWang.Proof.Campaign20260915.LowZeroMoment.abelApprox_fourteen_rational_error
#print axioms LiuWang.Proof.Campaign20260915.LowZeroMoment.cpow_critical_fourteen
#print axioms LiuWang.Proof.Campaign20260915.LowZeroMoment.endpoint_fourteen_strict_sign
#print axioms LiuWang.Proof.Campaign20260915.LowZeroMoment.exists_nontrivial_zero_fourteen_sixteen
#print axioms LiuWang.Proof.Campaign20260915.LowZeroMoment.fourteen_rpow_three_sub
#print axioms LiuWang.Proof.Campaign20260915.LowZeroMoment.gamma14AngleTerm_error
#print axioms LiuWang.Proof.Campaign20260915.LowZeroMoment.gamma14_argument_approx_formula
#print axioms LiuWang.Proof.Campaign20260915.LowZeroMoment.gamma14_argument_center_error
#print axioms LiuWang.Proof.Campaign20260915.LowZeroMoment.gamma14_argument_center_rational
#print axioms LiuWang.Proof.Campaign20260915.LowZeroMoment.gamma14_argument_rational_enclosure
#print axioms LiuWang.Proof.Campaign20260915.LowZeroMoment.gamma14_phase_im_neg
#print axioms LiuWang.Proof.Campaign20260915.LowZeroMoment.norm_zeta14Correction_le
#print axioms LiuWang.Proof.Campaign20260915.LowZeroMoment.power14Center_correct
#print axioms LiuWang.Proof.Campaign20260915.LowZeroMoment.power14Center_error
#print axioms LiuWang.Proof.Campaign20260915.LowZeroMoment.power14Phase_error
#print axioms LiuWang.Proof.Campaign20260915.LowZeroMoment.rsZeroMoment_le_third_div_fourteen
#print axioms LiuWang.Proof.Campaign20260915.LowZeroMoment.rsZeroMoment_sum_le_third_div_fourteen
#print axioms LiuWang.Proof.Campaign20260915.LowZeroMoment.xi_height_moment_le_third
#print axioms LiuWang.Proof.Campaign20260915.LowZeroMoment.xi_zero_height_gt_fourteen
#print axioms LiuWang.Proof.Campaign20260915.LowZeroMoment.zeta14Block0_upper
#print axioms LiuWang.Proof.Campaign20260915.LowZeroMoment.zeta14Block1_upper
#print axioms LiuWang.Proof.Campaign20260915.LowZeroMoment.zeta14Block2_upper
#print axioms LiuWang.Proof.Campaign20260915.LowZeroMoment.zeta14Block3_upper
#print axioms LiuWang.Proof.Campaign20260915.LowZeroMoment.zeta14Block4_upper
#print axioms LiuWang.Proof.Campaign20260915.LowZeroMoment.zeta14Block5_upper
#print axioms LiuWang.Proof.Campaign20260915.LowZeroMoment.zeta14Block6_upper
#print axioms LiuWang.Proof.Campaign20260915.LowZeroMoment.zeta14Block7_upper
#print axioms LiuWang.Proof.Campaign20260915.LowZeroMoment.zeta14Center_formula
#print axioms LiuWang.Proof.Campaign20260915.LowZeroMoment.zeta14Center_im_blocks
#print axioms LiuWang.Proof.Campaign20260915.LowZeroMoment.zeta14Center_im_upper
#print axioms LiuWang.Proof.Campaign20260915.LowZeroMoment.zeta14Correction_eq
#print axioms LiuWang.Proof.Campaign20260915.LowZeroMoment.zeta14TailIm_upper
#print axioms LiuWang.Proof.Campaign20260915.LowZeroMoment.zetaClosedValues_sixteen_pair_above_fourteen
#print axioms LiuWang.Proof.Campaign20260915.LowZeroMoment.zeta_fourteen_abel_error
#print axioms LiuWang.Proof.Campaign20260915.LowZeroMoment.zeta_fourteen_im_neg
#print axioms LiuWang.Proof.Campaign20260915.LowZeroMoment.zeta_fourteen_rational_error
#print axioms LiuWang.Proof.Campaign20260915.LowZeroMoment.zeta_zero_height_gt_fourteen
