import LiuWang.Proof.Campaign20260915.ZetaValidation.HankelContinuationCheck

/-! Parent audit of the actual Mellin/Hankel and local-integral components.
The Mellin identity is restricted to Re(s)>1. No critical-strip continuation,
infinite contour deformation, integer-saddle limit, or full R0 bound is asserted.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Complex Set MeasureTheory

namespace LiuWang.Proof.Campaign20260915.Parent.ZetaHankelAudit
open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem actual_zeta_tail (m : ℕ) {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = (∑ n ∈ Finset.range m, 1 / (n + 1 : ℂ) ^ s) +
      (∫ x : ℝ in Ioi 0, (x : ℂ) ^ (s - 1) *
        ((Real.exp (-(m : ℝ) * x) / (Real.exp x - 1) : ℝ) : ℂ)) / Gamma s :=
  zeta_eq_sum_add_mellin_tail m hs

theorem actual_tail_integrable {m : ℕ} (hm : 0 < m) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) * rsMellinTailKernel m x) (Ioi 0) :=
  rsMellinTail_integrable hm hs

#print axioms actual_zeta_tail
#print axioms actual_tail_integrable
end LiuWang.Proof.Campaign20260915.Parent.ZetaHankelAudit

#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.mem_rsRectanglePoles
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsDescentDirection_norm
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsDescentPoint_distance
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsDescent_denominator_lower
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsDescent_exponential_re
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsDescent_gaussian_re
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsDescent_no_integer
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsGaussian_descent_continuous
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsGaussian_tail_interval
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelBanks_actual_zeta
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelBanks_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelDenominator_analytic
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelDenominator_deriv_int
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelDenominator_zero_iff
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelKernel_analytic
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelKernel_meromorphic
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelKernel_order_int
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelKernel_pole_iff
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelKernel_pole_limit
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelKernel_rectangle
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelKernel_residue
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelKernel_saddle_factor
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelKernel_simple
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelLeftBank_limit
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelLog_analytic
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelLog_eq_principal
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelLog_left_limit
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelLog_neg
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelLog_pos
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelLog_right_limit
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelNumerator_analytic
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelNumerator_neg
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelNumerator_pos
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelRightBank_factor
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankelRightBank_limit
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankel_jump_ne_zero
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankel_local_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankel_local_truncation
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankel_local_truncation_pointwise
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankel_residue_jump_sum
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsHankel_residue_pair
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsJnIntegrand_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsJnIntegrand_continuousAt
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsJnOuterConstant_pos
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsJn_local_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsJn_outer_half_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsJn_outer_integrals
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsLocalPolynomial_continuous
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsMellinTailKernel_hasSum
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsMellinTail_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsMellinTail_mellin
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsSaddleRemainder_gaussian_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsSaddleScale_pos
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.rsSaddleScale_sq
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.zeta_eq_sum_add_hankel_banks
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.zeta_eq_sum_add_mellin_tail
