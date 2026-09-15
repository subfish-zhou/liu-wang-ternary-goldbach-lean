import LiuWang.Proof.ChebyshevBound.Consumer

/-! # 完整声明类型、实际定义值及公理锥；不包含尖锐 ψ 上界声明。 -/

open LiuWang.Proof.ChebyshevBound

#print Chebyshev.psi
#print ArithmeticFunction.vonMangoldt
#print abelPoleFactor

#check @norm_abel_integral_le
#check @zeta_eq_pole_mul_abel
#check @norm_zeta_pole_factor_sub_one_le
#check @riemannZeta_ne_zero_of_norm_sub_one_lt_re
#check @riemannZeta_ne_zero_of_im_sq_lt
#check @riemannZeta_ne_zero_low_rectangle
#check @analyticAt_abelPoleFactor
#check @re_lower_of_norm_sub_one_le
#check @norm_abelPoleFactor_sub_one_le_one
#check @two_thirds_le_norm_abelPoleFactor
#check @norm_deriv_abelPoleFactor_le_four
#check @norm_logDeriv_abelPoleFactor_le_six
#check @logDeriv_riemannZeta_add_pole_eq
#check @norm_logDeriv_riemannZeta_add_pole_le_eight
#check @norm_logDeriv_riemannZeta_real_le
#check @summable_mangoldt_dirichlet
#check @mangoldt_dirichlet_le_inv_add_eight
#check @source_abscissa_mem
#check @mangoldt_dirichlet_source_le
#check @sum_mangoldt_Icc_eq_psi
#check @sum_mangoldt_sq_le_log_mul_psi
#check @sum_mangoldt_sq_subset_le_log_mul_psi
#check @source_weighted_mangoldt_consumer
#check @window_subset_mangoldt_prefix
#check @source_window_square_mass_consumer
#check @source_exponential_sum_consumer
#check @low_height_zeta_consumer

#print axioms abelPoleFactor
#print axioms norm_abel_integral_le
#print axioms zeta_eq_pole_mul_abel
#print axioms norm_zeta_pole_factor_sub_one_le
#print axioms riemannZeta_ne_zero_of_norm_sub_one_lt_re
#print axioms riemannZeta_ne_zero_of_im_sq_lt
#print axioms riemannZeta_ne_zero_low_rectangle
#print axioms analyticAt_abelPoleFactor
#print axioms re_lower_of_norm_sub_one_le
#print axioms norm_abelPoleFactor_sub_one_le_one
#print axioms two_thirds_le_norm_abelPoleFactor
#print axioms norm_deriv_abelPoleFactor_le_four
#print axioms norm_logDeriv_abelPoleFactor_le_six
#print axioms logDeriv_riemannZeta_add_pole_eq
#print axioms norm_logDeriv_riemannZeta_add_pole_le_eight
#print axioms norm_logDeriv_riemannZeta_real_le
#print axioms summable_mangoldt_dirichlet
#print axioms mangoldt_dirichlet_le_inv_add_eight
#print axioms source_abscissa_mem
#print axioms mangoldt_dirichlet_source_le
#print axioms sum_mangoldt_Icc_eq_psi
#print axioms sum_mangoldt_sq_le_log_mul_psi
#print axioms sum_mangoldt_sq_subset_le_log_mul_psi
#print axioms source_weighted_mangoldt_consumer
#print axioms window_subset_mangoldt_prefix
#print axioms source_window_square_mass_consumer
#print axioms source_exponential_sum_consumer
#print axioms low_height_zeta_consumer
