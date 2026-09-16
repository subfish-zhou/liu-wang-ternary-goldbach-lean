import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightPhase
import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.FiveFourthsBudget

set_option autoImplicit false
set_option Elab.async false
noncomputable section

open Complex

namespace LiuWang.Proof.Campaign20260915.RosserCount

open LiuWang.Proof.Campaign20260915.Totient
open LiuWang.Proof.Campaign20260915.ZetaWinding

theorem backlund_center_phase_lt_half_pi (T : ℝ) :
    |(backlundLog T (5 / 4)).im| < Real.pi / 2 := by
  have hs : Real.log ‖riemannZeta ((5 / 4 : ℝ) : ℂ)‖ ≤ 15261 / 10000 :=
    LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.realLogZeta_fiveFourths_upper
  have hp := (abs_im_le_norm (backlundLog T (5 / 4))).trans
    ((norm_backlundLog_le_real_log_zeta T (by norm_num : (1 : ℝ) < 5 / 4)
      (by norm_num : (5 / 4 : ℝ) ≤ 2)).trans hs)
  linarith [Real.pi_gt_d2]

theorem positiveCount_backlund_source_integral_bound {T : ℝ} (hT : rsA ≤ T)
    (hr : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = T → riemannZeta s ≠ 0) :
    |(positiveCount T : ℝ) - rosserMain T| <
      (Real.circleAverage (backlundCircleEnvelope T) 0 (33 / 25 : ℝ) -
        Real.log ‖riemannZeta (backlundCenterPoint T)‖) /
          (2 * Real.log (44 / 25 : ℝ)) +
      1 / 2 + 4 / (Real.pi * T) + |rosserGammaRemainder T| / Real.pi := by
  have hp : |(backlundLog T (5 / 4)).im| / Real.pi ≤ 1 / 2 := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    linarith [backlund_center_phase_lt_half_pi T]
  exact (positiveCount_backlund_integral_bound hT hr).trans_le
    (add_le_add (add_le_add (add_le_add le_rfl hp) le_rfl) le_rfl)

#print axioms backlund_center_phase_lt_half_pi
#print axioms positiveCount_backlund_source_integral_bound

end LiuWang.Proof.Campaign20260915.RosserCount
