import LiuWang.Proof.Campaign20260915.ZetaValidation.FixedHankelCheck

/-! Parent audit: actual zeta representation on the whole upper half-plane.
This is a representation theorem, not a certified evaluator or a zero count.
The saddle contour deformation and original remainder budgets remain unpaid.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Complex

namespace LiuWang.Proof.Campaign20260915.Parent.FixedHankelAudit
open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem actual_upper_half_plane_representation {m : ℕ} (hm : 0 < m)
    {s : ℂ} (ht : 0 < s.im) {u : ℝ} (hu : u < 0) :
    riemannZeta s = (∑ n ∈ Finset.range m, 1 / (n + 1 : ℂ) ^ s) +
      rsHankelPrefactor s * rsHankelTiltedC1 s m u :=
  zeta_eq_sum_add_tilted_hankel hm ht hu

#print axioms actual_upper_half_plane_representation
end LiuWang.Proof.Campaign20260915.Parent.FixedHankelAudit

#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsFiniteDirichletSum_differentiable
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelArcBetween_add
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelArcBetween_continuous
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelArcBetween_tendsto_zero
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelArc_actual_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelArc_actual_integral
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelArc_difference
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelArc_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelArc_parameter_deriv
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelArc_small_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelArc_tendsto_zero
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelBank_tail_differentiable
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelBanks_tail_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelC1_differentiable
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelC1_eq_tilted
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelC1_initial_actual_banks
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelC1_initial_independent
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelC1_radius_independent
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelDenominator_ne_zero_of_norm
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelDenominator_small_lower
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelLeftBank_integral_approach
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelLift_actual
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelLift_analytic
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelLift_analytic_lower
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelLift_bottom
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelLift_joint_continuous
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelLift_parameter_deriv
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelLift_sector_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelLift_small_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelLift_top
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelLog_exp
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelPrefactor_differentiableAt
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelPrefactor_eq
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelRay_actual
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelRay_bottom_integral
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelRay_continuous
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelRay_continuousOn_sector
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelRay_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelRay_rotation
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelRay_top_integral
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelRightBank_integral_approach
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelSector_majorant_tendsto
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelSector_rectangle
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelTiltedC1_actual
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelTilted_tails_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankel_left_sector_sin
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankel_right_sector_sin
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsScaledMellin_continuous
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsScaledMellin_tail_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsTruncatedMellin_convergent
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsTruncatedMellin_differentiable
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsTruncatedMellin_eq_integral
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsTruncatedMellin_exp_decay
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsTruncatedMellin_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsTruncatedMellin_zero_near_origin
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.zeta_eq_fixed_hankel_upper
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.zeta_eq_sum_add_fixed_hankel
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.zeta_eq_sum_add_fixed_hankel_critical_strip
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.zeta_eq_sum_add_tilted_hankel
