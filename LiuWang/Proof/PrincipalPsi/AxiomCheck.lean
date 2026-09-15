import LiuWang.Proof.PrincipalPsi.Consumer

/-! # 主字符已编译前缀的完整类型、定义与标准公理审计 -/

set_option format.width 120
set_option pp.universes true

open LiuWang.Proof.PrincipalPsi

#print regularizedPrincipal
#print principalEuler
#print PrincipalZeroIndex
#print principalZeroValue
#print closedZeroSet
#print closedZeroIndices
#print highZeroIndices
#print lowZeroIndices
#print highZeroValues
#print highZeroSum
#print zetaCenteredIntegrand
#print closedCenteredZeroSum
#print zetaRightIntegral

#check @regularizedPrincipal_eq
#check @analytic_regularizedPrincipal
#check @regularizedPrincipal_one_ne_zero
#check @principal_eq_regularized_div
#check @principal_eq_regularized_div_nhdsNE
#check @meromorphic_principal
#check @meromorphicOrderAt_principal_one
#check @meromorphicOrderAt_principal_ne_top
#check @meromorphic_principal_logDeriv
#check @simple_principal_logDeriv
#check @principal_centered_residue_one
#check @zeta_centered_residue_one
#check @zeta_centered_kernel_at_pole
#check @differentiable_principalEuler
#check @principalEuler_ne_zero
#check @principal_eq_euler_mul_zeta
#check @principal_eq_euler_mul_zeta_nhds
#check @analytic_principal_of_ne_one
#check @analytic_zeta_of_ne_one
#check @principal_zero_iff_zeta_zero
#check @analyticOrderAt_principal_eq_zeta
#check @analyticOrderNatAt_principal_eq_zeta
#check @analyticOrderAt_regularized_eq_principal
#check @analyticOrderNatAt_regularized_eq_principal
#check @regularizedPrincipal_zero_at_index
#check @principalZeroValue_ne_one
#check @principal_zero_at_index
#check @closedZeroSet_finite
#check @mem_closedZeroIndices
#check @mem_highZeroIndices
#check @sum_closed_eq_low_add_high
#check @mem_highZeroValues
#check @highZeroValues_eq_zeta
#check @highZeroFiber_card
#check @sum_highZeroValues_multiplicity
#check @highZeroSum_eq_zeta
#check @zetaCenteredIntegrand_eq
#check @meromorphic_zetaCenteredIntegrand
#check @simple_zetaCenteredIntegrand
#check @analytic_zetaCenteredIntegrand
#check @residue_zetaCenteredIntegrand_one
#check @residue_zetaCenteredIntegrand_of_ne_one
#check @residue_zetaCenteredIntegrand_zero
#check @zetaCenteredIntegrand_poles_subset
#check @closedCentered_sub_high_eq
#check @norm_low_centered_sum_le_card
#check @norm_high_center_sum_le_card
#check @norm_closedCentered_sub_high_le_card
#check @psi_mod_one_eq_chebyshev
#check @zetaRightIntegral_eq_principal
#check @zeta_right_perron_strong
#check @pole_center_cost_le_source
#check @zeta_psi_remainder_ledger

#print axioms regularizedPrincipal_eq
#print axioms analytic_regularizedPrincipal
#print axioms regularizedPrincipal_one_ne_zero
#print axioms principal_eq_regularized_div
#print axioms principal_eq_regularized_div_nhdsNE
#print axioms meromorphic_principal
#print axioms meromorphicOrderAt_principal_one
#print axioms meromorphicOrderAt_principal_ne_top
#print axioms meromorphic_principal_logDeriv
#print axioms simple_principal_logDeriv
#print axioms principal_centered_residue_one
#print axioms zeta_centered_residue_one
#print axioms zeta_centered_kernel_at_pole
#print axioms differentiable_principalEuler
#print axioms principalEuler_ne_zero
#print axioms principal_eq_euler_mul_zeta
#print axioms principal_eq_euler_mul_zeta_nhds
#print axioms analytic_principal_of_ne_one
#print axioms analytic_zeta_of_ne_one
#print axioms principal_zero_iff_zeta_zero
#print axioms analyticOrderAt_principal_eq_zeta
#print axioms analyticOrderNatAt_principal_eq_zeta
#print axioms analyticOrderAt_regularized_eq_principal
#print axioms analyticOrderNatAt_regularized_eq_principal
#print axioms regularizedPrincipal_zero_at_index
#print axioms principalZeroValue_ne_one
#print axioms principal_zero_at_index
#print axioms closedZeroSet_finite
#print axioms mem_closedZeroIndices
#print axioms mem_highZeroIndices
#print axioms sum_closed_eq_low_add_high
#print axioms mem_highZeroValues
#print axioms highZeroValues_eq_zeta
#print axioms highZeroFiber_card
#print axioms sum_highZeroValues_multiplicity
#print axioms highZeroSum_eq_zeta
#print axioms zetaCenteredIntegrand_eq
#print axioms meromorphic_zetaCenteredIntegrand
#print axioms simple_zetaCenteredIntegrand
#print axioms analytic_zetaCenteredIntegrand
#print axioms residue_zetaCenteredIntegrand_one
#print axioms residue_zetaCenteredIntegrand_of_ne_one
#print axioms residue_zetaCenteredIntegrand_zero
#print axioms zetaCenteredIntegrand_poles_subset
#print axioms closedCentered_sub_high_eq
#print axioms norm_low_centered_sum_le_card
#print axioms norm_high_center_sum_le_card
#print axioms norm_closedCentered_sub_high_le_card
#print axioms psi_mod_one_eq_chebyshev
#print axioms zetaRightIntegral_eq_principal
#print axioms zeta_right_perron_strong
#print axioms pole_center_cost_le_source
#print axioms zeta_psi_remainder_ledger
