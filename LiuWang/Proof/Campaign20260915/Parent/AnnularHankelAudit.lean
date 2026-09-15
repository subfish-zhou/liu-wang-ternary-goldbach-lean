import LiuWang.Proof.Campaign20260915.ZetaValidation.AnnularHankelCheck

/-! Parent consumption of the complete finite pole crossing.
The remaining contour is the expanded circular Hankel contour, not the saddle C2.
C2 convergence does not imply its equality to that contour or an effective remainder.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Complex

namespace LiuWang.Proof.Campaign20260915.Parent.AnnularHankelAudit
open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem actual_zeta_after_pole_crossing {m : ℕ} (hm : 0 < m)
    {s : ℂ} (ht : 0 < s.im) {R : ℝ} (hR : (m : ℝ) < R) (hR' : R < m + 1) :
    riemannZeta s = (∑ n ∈ Finset.range m, 1 / (n + 1 : ℂ) ^ s) +
      (2 * Real.pi : ℂ) ^ s / (2 * Gamma s * cos (Real.pi * s / 2)) *
        (∑ k ∈ Finset.range m, (k + 1 : ℂ) ^ (s - 1)) +
      rsHankelPrefactor s * rsHankelTiltedC1 s m (Real.log R) :=
  zeta_eq_source_sums_add_expanded_hankel hm ht hR hR'

#print axioms actual_zeta_after_pole_crossing
end LiuWang.Proof.Campaign20260915.Parent.AnnularHankelAudit

#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.exp_rsHankelLog
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsC2Corner_coordinates
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsC2Corner_upper
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsC2LeftPoint_coordinates
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsC2LeftPoint_endpoints
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsC2Left_avoids_cut
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsC2Left_depth
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsC2Left_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsC2Left_kernel_analytic
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsC2Left_no_integer
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsC2Right_depth
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsC2Right_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsC2Right_kernel_analytic
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsC2_connectors_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsC2_connectors_limit
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelExpanded_arc_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelKernel_analytic_slit
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelKernel_lower_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelLift_analytic_off
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelLift_annulus_jump
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelLift_annulus_residues
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelLift_meromorphic
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelLift_order_pole
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelLift_pole_iff
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelLift_residue
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelLog_coordinates_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelLog_int_im
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelLog_int_injective
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelLog_int_re
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelTiltedC1_annulus
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankel_affine_connector_limit
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankel_affine_tail_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankel_horizontal_connector_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankel_second_prefactor
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsLiftDenominator_deriv
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsLiftDenominator_zero_iff
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsLiftNumerator_pole
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsLiftPoleIndices_sum
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsLiftPole_mem_rectangle
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsLiftPole_strict_interior
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsSourceC2_local_split
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsSourceC2_local_truncation
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsSourceC2_truncation_limit
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.zeta_eq_source_sums_add_expanded_hankel
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.zeta_eq_sum_add_expanded_hankel
