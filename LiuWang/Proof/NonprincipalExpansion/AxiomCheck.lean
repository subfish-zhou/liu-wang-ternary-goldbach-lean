import LiuWang.Proof.NonprincipalExpansion.Consumer

/-! # 完整公开类型、实际定义和标准公理闭包 -/

set_option autoImplicit false
set_option pp.universes true
set_option pp.fullNames true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.deepTerms true
set_option format.width 120

open LiuWang.Proof.NonprincipalExpansion

#check @lower_nonneg
#check @lower_le
#check @mem_window_real
#check @sum_window_eq_Ioc_add_lower
#check @sum_prefix_zero
#check @phaseDerivative_continuous
#check @prefix_phase_integrable
#check @closed_window_abel
#check @S_chi_abel
#check @psi_phase_integrable
#check @abelTransform_add
#check @cpow_div_hasDerivAt
#check @cpow_continuousOn
#check @cpow_phase_integrable
#check @Jrho_eq_abelTransform
#check @abelTransform_sum
#check @high_zero_ne_zero
#check @highZeroSum_phase_integrable
#check @sum_Jrho_eq_abelTransform
#check @expansion_error_identity
#check @norm_phaseDerivative
#check @norm_phase_error_integral_le
#check @norm_abelTransform_le
#check @norm_lowerTerm_le_log
#check @lowerTerm_cost_source_le
#check @norm_lowerTerm_source_le
#check @source_abel_budget
#check @S_chi_eq_twistedS
#check @nonprincipal_expansion_source_strong
#check @nonprincipal_expansion_source
#check @nonprincipal_expansion
#check @nonprincipal_twistedS_expansion

#print axioms closed_window_abel
#print axioms cpow_div_hasDerivAt
#print axioms sum_Jrho_eq_abelTransform
#print axioms expansion_error_identity
#print axioms norm_phase_error_integral_le
#print axioms lowerTerm_cost_source_le
#print axioms nonprincipal_expansion_source_strong
#print axioms nonprincipal_expansion_source
#print axioms nonprincipal_expansion
#print axioms nonprincipal_twistedS_expansion

#print phaseDerivative
#print abelTransform
#print lowerTerm
#print S_chi
#print LiuWang.Proof.Interfaces.Jrho
#print LiuWang.Proof.Interfaces.sourceL
#print LiuWang.Proof.Interfaces.sourceT
#print LiuWang.Proof.Interfaces.sourceP1
#print LiuWang.Proof.Interfaces.sourceWindowLower
#print LiuWang.Proof.Interfaces.windowFinset
#print LiuWang.Fourier.liuWangSupport
#print AnalyticNumberTheory.LargeSieve.charReal
#print LiuWang.Proof.CharacterExpansion.twistedS
#print LiuWang.Proof.ExplicitPerron.psi
#print BombieriVinogradov.SiegelWalfisz.characterChebyshevSum
#print LiuWang.Proof.FixedHeightZeroSum.highZeroSum
#print LiuWang.Proof.FixedHeightZeroSum.highZeroIndices
#print LiuWang.Proof.FixedHeightZeroSum.fixedZeroIndices
#print LiuWang.Proof.Interfaces.criticalZeroIndices
#print LiuWang.Proof.Interfaces.CompletedZeroIndex
#print LiuWang.Proof.Interfaces.completedZeroValue
#print BombieriVinogradov.SiegelWalfisz.SymmetricCompletedZeroIndex
#print BombieriVinogradov.SiegelWalfisz.symmetricCompletedLFunction
#print Complex.Hadamard.divisorZeroIndex₀
#print Complex.Hadamard.divisorZeroIndex

#check @sum_mul_eq_sub_sub_integral_mul
#check @integrableOn_mul_sum_Icc
#check @intervalIntegral.integral_mul_deriv_eq_deriv_mul
#check @intervalIntegral.integral_finsetSum
#check @integral_id
#check @LiuWang.Proof.NonprincipalPsi.psi_highZeroSum_source_le_strong
#print axioms LiuWang.Proof.NonprincipalPsi.psi_highZeroSum_source_le_strong
#check @LiuWang.Proof.NonprincipalPsi.mem_highZeroIndices_nonprincipal
#check @LiuWang.Proof.PerronBudget.million_sourceT_sq_le_endpoint
#print axioms LiuWang.Proof.PerronBudget.million_sourceT_sq_le_endpoint
