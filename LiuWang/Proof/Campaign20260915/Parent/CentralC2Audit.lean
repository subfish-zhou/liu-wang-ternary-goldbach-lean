import LiuWang.Proof.Campaign20260915.ZetaValidation.CentralContourCheck

/-! Actual zeta now uses the source C2 contour, not a presumed contour equality.
This noninteger window does not discharge the integer-eta continuation or total remainder.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Complex
namespace LiuWang.Proof.Campaign20260915.Parent.CentralC2Audit
open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem actual_zeta_C2 {m : ℕ} (hm : 0 < m) {s : ℂ}
    (ht : 0 < s.im) (hs : s.re ≤ 1) {eta : ℝ}
    (hlo : (m : ℝ) < eta) (hhi : eta < m + 1) :
    riemannZeta s = (∑ n ∈ Finset.range m, 1 / (n + 1 : ℂ) ^ s) +
      (2 * Real.pi : ℂ) ^ s / (2 * Gamma s * cos (Real.pi * s / 2)) *
        (∑ k ∈ Finset.range m, (k + 1 : ℂ) ^ (s - 1)) +
      rsHankelPrefactor s * rsSourceC2 s eta m :=
  zeta_eq_source_sums_add_C2 hm ht hs hlo hhi

#print axioms actual_zeta_C2
end LiuWang.Proof.Campaign20260915.Parent.CentralC2Audit

#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.central_exact_convex
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.central_exact_union
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsCentralCircularTruncation_limit
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsCentralCircularTruncation_primitive
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsCentralDomain_exact
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsCentralDomain_kernel_analytic
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsCentralDomain_mem_iff
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsCentralDomain_mem_of_cut
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsCentralDomain_open
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsCentralPrimitive_deriv
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsCentralSourceTruncation_limit
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsCentralSourceTruncation_primitive
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsCentral_arc_integral
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsCentral_arc_mem
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsCentral_finite_contour_identity
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsCentral_horizontal_integral
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsCentral_horizontal_mem
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsCentral_left_integral
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsCentral_left_mem
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsCentral_line_integral
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsCentral_patches_convex
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsCentral_patches_open
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsCentral_path_integral
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsCentral_ray_endpoints
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsCentral_ray_integral
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsCentral_ray_mem
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsCentral_right_integral
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsCentral_right_mem
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelTiltedC1_eq_sourceC2
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankel_exp_avoids_cut
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.zeta_eq_C2_local_split
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.zeta_eq_source_local_truncation
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.zeta_eq_source_sums_add_C2
