import LiuWang.Proof.Campaign20260915.RosserCount.BacklundClosedCount

set_option autoImplicit false
noncomputable section

open Complex
open LiuWang.Proof.Campaign20260915.Totient
open LiuWang.Proof.Campaign20260915.ZetaWinding

namespace LiuWang.Proof.Campaign20260915.RosserCount

theorem backlund_real_center_log_upper :
    Real.log ‖riemannZeta (5 / 4 : ℂ)‖ ≤ 3821 / 2500 := by
  have h := backlund_zeta_dirichlet_envelope (s := (5 / 4 : ℂ))
    (by norm_num) (N := 16) (by norm_num)
  norm_num only [show (5 / 4 : ℂ).re = (5 / 4 : ℝ) by norm_num] at h
  have hz : riemannZeta (5 / 4 : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  exact (Real.log_le_log (norm_pos_iff.mpr hz) h).trans backlund_right_cell64_scalar

theorem backlund_center_phase_from_circle (T : ℝ) :
    |(backlundLog T (5 / 4)).im| < Real.pi / 2 := by
  have h := (abs_im_le_norm (backlundLog T (5 / 4))).trans
    ((norm_backlundLog_le_real_log_zeta T (by norm_num : (1 : ℝ) < 5 / 4)
      (by norm_num : (5 / 4 : ℝ) ≤ 2)).trans (by simpa using backlund_real_center_log_upper))
  linarith [Real.pi_gt_d2]

theorem positiveCount_backlund_source_phase_from_circle {T : ℝ} (hT : rsA ≤ T)
    (hr : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = T → riemannZeta s ≠ 0) :
    |(positiveCount T : ℝ) - rosserMain T| <
      (Real.circleAverage (backlundCircleEnvelope T) 0 (33 / 25 : ℝ) -
        Real.log ‖riemannZeta (backlundCenterPoint T)‖) /
          (2 * Real.log (44 / 25 : ℝ)) +
      1 / 2 + 4 / (Real.pi * T) + |rosserGammaRemainder T| / Real.pi := by
  have hp : |(backlundLog T (5 / 4)).im| / Real.pi ≤ 1 / 2 := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    linarith [backlund_center_phase_from_circle T]
  exact (positiveCount_backlund_integral_bound hT hr).trans_le
    (add_le_add (add_le_add (add_le_add le_rfl hp) le_rfl) le_rfl)

#print axioms backlund_real_center_log_upper
#print axioms backlund_center_phase_from_circle
#print axioms positiveCount_backlund_source_phase_from_circle

end LiuWang.Proof.Campaign20260915.RosserCount
