import LiuWang.Proof.Campaign20260915.ZetaLehmanKernel.ZeroSeries

/-! Original 1.48 paired kernel, full multiplicity-preserving sum and actual horizontal zeta mass.
The two previously delivered winding interfaces are accepted together in this parent handoff.
Gamma, pole and right-hand zeta integrals remain explicit; this is not the total Turing budget.
-/
set_option autoImplicit false
set_option Elab.async false

#print axioms LiuWang.Proof.Campaign20260915.ZetaLehmanKernel.radialMajorant_hasDerivAt
#print axioms LiuWang.Proof.Campaign20260915.ZetaLehmanKernel.radialMajorant_monotone
#print axioms LiuWang.Proof.Campaign20260915.ZetaLehmanKernel.logRadius_shift_le
#print axioms LiuWang.Proof.Campaign20260915.ZetaLehmanKernel.logRadius_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaLehmanKernel.logRadius_shift_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaLehmanKernel.zeroLoss_eq_integral
#print axioms LiuWang.Proof.Campaign20260915.ZetaLehmanKernel.zeroLoss_lift
#print axioms LiuWang.Proof.Campaign20260915.ZetaLehmanKernel.zeroLoss_pair_real
#print axioms LiuWang.Proof.Campaign20260915.ZetaLehmanKernel.logNormPrimitive_zero_hasDerivAt
#print axioms LiuWang.Proof.Campaign20260915.ZetaLehmanKernel.realPair_hasDerivAt
#print axioms LiuWang.Proof.Campaign20260915.ZetaLehmanKernel.realPair_antitone
#print axioms LiuWang.Proof.Campaign20260915.ZetaLehmanKernel.realPair_neg
#print axioms LiuWang.Proof.Campaign20260915.ZetaLehmanKernel.zeroLoss_pair_real_le
#print axioms LiuWang.Proof.Campaign20260915.ZetaLehmanKernel.zeroLoss_pair_lift
#print axioms LiuWang.Proof.Campaign20260915.ZetaLehmanKernel.lehman_polynomial_nonneg
#print axioms LiuWang.Proof.Campaign20260915.ZetaLehmanKernel.lehman_rational_budget
#print axioms LiuWang.Proof.Campaign20260915.ZetaLehmanKernel.referencePair_eq
#print axioms LiuWang.Proof.Campaign20260915.ZetaLehmanKernel.zeroLoss_pair_lehman
#print axioms LiuWang.Proof.Campaign20260915.ZetaLehmanKernel.zeroIntegral_eq_neg_loss
#print axioms LiuWang.Proof.Campaign20260915.ZetaLehmanKernel.referenceTerm_eq
#print axioms LiuWang.Proof.Campaign20260915.ZetaLehmanKernel.zeroIntegral_pair_lehman
#print axioms LiuWang.Proof.Campaign20260915.ZetaLehmanKernel.xi_reference_ne_zero
#print axioms LiuWang.Proof.Campaign20260915.ZetaLehmanKernel.xi_zero_pair_lehman
#print axioms LiuWang.Proof.Campaign20260915.ZetaLehmanKernel.xi_zero_series_lehman
#print axioms LiuWang.Proof.Campaign20260915.ZetaLehmanKernel.xi_lehman_log_integral_lower
#print axioms LiuWang.Proof.Campaign20260915.ZetaLehmanKernel.horizontalLogMass_lehman_lower
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.xi_uncompensated_logDeriv_summable
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.xi_uncompensated_logDeriv
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.xi_uncompensated_integral_summable
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.xi_uncompensated_horizontal_difference
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.xi_lehman_uncompensated_series
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.xi_log_norm_zeta_factors
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.lehman_zeta_factor_ratio
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.lehmanGammaLog_continuousOn
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.lehmanGammaLog_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.lehmanPoleLog_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.zeta_lehman_unit_shift_integral
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.horizontalLogMass_lehman_zero_series
