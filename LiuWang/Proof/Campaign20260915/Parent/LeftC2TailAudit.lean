import LiuWang.Proof.Campaign20260915.ZetaC2LeftTail.Check

/-! Actual left infinite branch, including its negative-real-axis crossing.
The numerical allowance here is for the left branch, not the complete remainder.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Complex Set MeasureTheory
namespace LiuWang.Proof.Campaign20260915.Parent.LeftC2TailAudit
open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaC2LeftTail

theorem actual_prefactored_left_tail {s : ℂ} {eta : ℝ}
    (he : 10 ≤ eta) (hs : s.re = 1 / 2) (ht : s.im = 2 * Real.pi * eta ^ 2) :
    ‖rsHankelPrefactor s * ∫ r : ℝ in Ioi 0, rsC2LeftIntegrand s eta ⌊eta⌋₊ r‖ ≤
      1 / (10 * eta ^ 4) :=
  left_hankel_floor_budget he hs ht

#print axioms actual_prefactored_left_tail
end LiuWang.Proof.Campaign20260915.Parent.LeftC2TailAudit

#print axioms LiuWang.Proof.Campaign20260915.ZetaC2LeftTail.corner_im_bounds
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2LeftTail.corner_re_add_im
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2LeftTail.left_norm_ge_one
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2LeftTail.left_direction_norm
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2LeftTail.left_axis_window
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2LeftTail.arctan_eight_fifteenths
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2LeftTail.left_log_im_lower
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2LeftTail.denominator_upper_strip
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2LeftTail.denominator_lower_strip
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2LeftTail.denominator_half_integer_window
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2LeftTail.left_denominator_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2LeftTail.left_numerator_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2LeftTail.left_integrand_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2LeftTail.left_decay_rate
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2LeftTail.left_integral_norm_budget
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2LeftTail.left_integral_budget
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2LeftTail.critical_gamma_norm_sq
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2LeftTail.critical_hankel_jump_norm
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2LeftTail.critical_hankel_numerator_norm_sq
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2LeftTail.critical_hankel_prefactor_norm_sq
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2LeftTail.critical_hankel_prefactor_norm_le_one
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2LeftTail.left_exp_scalar
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2LeftTail.left_hankel_exponential
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2LeftTail.left_hankel_floor_budget
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2LeftTail.left_scalar_original_scale
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2LeftTail.left_hankel_R0
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2LeftTail.left_hankel_R2
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2LeftTail.saddle_critical_coordinates
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2LeftTail.source_local_left_identity
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2LeftTail.source_local_truncation_left_budget
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2LeftTail.source_R0_left_budget
#print axioms LiuWang.Proof.Campaign20260915.ZetaC2LeftTail.source_R2_left_budget
