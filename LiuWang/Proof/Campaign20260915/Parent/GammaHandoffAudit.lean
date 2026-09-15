import LiuWang.Proof.Campaign20260915.ZetaWinding.LehmanReferenceBudget
import LiuWang.Proof.Campaign20260915.ZetaLehmanKernel.ZeroSeries
import LiuWang.Proof.Campaign20260915.ZetaValidation.GammaStirlingPhase
import LiuWang.Proof.DirichletZeroCount.Remainder.Trapezoid

/-! Actual Gamma and reference-mass budgets consumed in the horizontal zeta lower bound.
Pole and right zeta integrals remain explicit. This is not the full Turing estimate.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Complex MeasureTheory Set
namespace LiuWang.Proof.Campaign20260915.Parent.GammaHandoffAudit
open LiuWang.Proof.Campaign20260915.ZetaWinding
open LiuWang.Proof.Campaign20260915.ZetaLehmanKernel

 theorem actual_horizontal_gamma_reference_paid {T : ℝ} (hT : 168 * Real.pi < T) :
    -(37 / 25 : ℝ) * (-(logDeriv riemannZeta (3 / 2)).re +
      Real.log (T / (2 * Real.pi)) / 2 + 1 / 10000) +
      Real.log (T / 2) / 2 - 9 / 100000 +
      (∫ x in (1 / 2 : ℝ)..(3 / 2), lehmanPoleLog T x) - Real.log Real.pi / 2 +
      (∫ x in Ioi (3 / 2 : ℝ), Real.log ‖riemannZeta (horizontalAt T x)‖) +
      (∫ x in (3 / 2 : ℝ)..(5 / 2), Real.log ‖riemannZeta (horizontalAt T x)‖) <
        horizontalLogMass T := by
  have ht : 0 < T := lt_trans (by positivity) hT
  have hm := horizontalLogMass_lehman_lower ht.ne'
  have hr := lehman_reference_mass_upper hT
  rw [← xi_uncompensated_logDeriv (xi_reference_ne_zero T)] at hr
  have hg := (abs_lt.mp (lehmanGamma_original_budget hT)).2
  linarith

 theorem existing_logGamma_stirling_im_error {z : ℂ} (hz : 0 < z.re) (ht : 0 ≤ z.im) :
    |(LiuWang.Proof.DirichletZeroCount.Remainder.logGamma z).im -
      LiuWang.Proof.DirichletZeroCount.Remainder.stirlingPhase z| ≤
      z.im / (8 * normSq z) := by
  have h := LiuWang.Proof.Campaign20260915.ZetaValidation.gammaStirlingPhase_error hz ht
  change 0 ≤ LiuWang.Proof.DirichletZeroCount.Remainder.stirlingPhase z -
      (LiuWang.Proof.DirichletZeroCount.Remainder.logGamma z).im ∧
      LiuWang.Proof.DirichletZeroCount.Remainder.stirlingPhase z -
      (LiuWang.Proof.DirichletZeroCount.Remainder.logGamma z).im ≤ z.im / (8 * normSq z) at h
  rw [abs_of_nonpos (by linarith [h.1])]
  linarith [h.2]

#print axioms actual_horizontal_gamma_reference_paid
#print axioms existing_logGamma_stirling_im_error
end LiuWang.Proof.Campaign20260915.Parent.GammaHandoffAudit

#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.trapezoid_unit_abs
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.trapezoid_sum_abs
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.reciprocalProfile
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.reciprocalSlope
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.reciprocalCurvature
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.reciprocalEnvelope
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.reciprocalPrimitive
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.reciprocalEnvelopePrimitive
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.reciprocalProfile_derivatives
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.reciprocalPrimitive_derivatives
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.reciprocalCurvature_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.reciprocal_quadrature_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.reciprocalProfile_tendsto_zero
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.reciprocalPrimitive_log_boundary
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.digamma_reciprocal_partial_sums
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.digamma_re_stirling_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.log_norm_sub_log_im_bounds
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.digamma_re_log_im_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.lehman_digamma_uniform_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.gamma_log_norm_horizontal_derivative
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.lehmanGammaLog_pointwise_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.lehmanGamma_integral_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.lehmanGamma_original_budget
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.zeta_logDeriv_norm_le_real
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.lehman_reference_mass_identity
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.lehman_reference_mass_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.lehman_reference_original_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.lehman_reference_mass_upper
