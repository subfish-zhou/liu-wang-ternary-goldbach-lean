import LiuWang.Proof.PrincipalPsi.Quantitative.PrincipalFormula

/-! # 主字符定量公式：公开类型、真实定义与终端公理检查 -/

set_option format.width 120
set_option pp.universes true

open LiuWang.Proof.PrincipalPsi.Quantitative

#print xiFactor
#print xiWindowSet
#print xiWindow
#print referenceMass
#print heightSeparationBudget
#print xiWindowValues
#print principalClosedValues
#print horizontalLogBound
#print xiRectangleIndices
#print xiRectangleValues
#print xiRectangleCenteredSum
#print changedXiIndices

#check @analytic_xiFactor
#check @xiFactor_ne_zero
#check @xi_eq_factor_regularized
#check @xi_eq_factor_regularized_nhds
#check @analyticOrderAt_xi_eq_regularized
#check @analyticOrderNatAt_xi_eq_regularized
#check @analyticOrderNatAt_xi_eq_principal
#check @xi_zero_iff_regularized_zero
#check @xi_zero_iff_zeta_zero
#check @zeta_zero_strip
#check @zeta_ne_zero_left
#check @xiWindowSet_finite
#check @mem_xiWindow
#check @referenceMass_nonneg
#check @xi_reference_kernel_sum_le
#check @local_kernel_lower
#check @xiWindow_local_card_le
#check @xiWindow_total_card_le
#check @exists_xi_separated_height
#check @heightSeparationBudget_pos
#check @exists_xi_rectangle_heights
#check @mem_xiWindowValues
#check @xiWindow_fiber_card
#check @sum_xiWindow_values
#check @principalClosedValues_eq_xiWindowValues
#check @principalClosed_fiber_card
#check @sum_principal_closed_eq_xi
#check @card_principal_closed_eq_xi
#check @principal_closed_card_le
#check @norm_closedCentered_sub_high_le
#check @xiFactor_eq
#check @logDeriv_xiFactor
#check @logDeriv_xi_eq_zeta
#check @xi_hadamard_logDeriv
#check @xi_reciprocal_difference_summable
#check @zeta_logDeriv_difference
#check @norm_xi_reciprocal_difference_separated
#check @zeta_ne_zero_separated
#check @norm_logDeriv_zeta_separated
#check @norm_logDeriv_xi_zero_le
#check @norm_xiTerm_left_le
#check @norm_logDeriv_zeta_left
#check @norm_zetaCenteredIntegrand_left
#check @mem_xiRectangleIndices
#check @xiRectangle_fiber_card
#check @sum_xiRectangle_values
#check @zeta_rectangle_residue
#check @zeta_selected_border
#check @zetaRightIntegral_eq_vertical
#check @zeta_right_add_rectangle_zeros
#check @changedXiIndices_edge
#check @changedXiIndices_card_le
#check @norm_transport_to_closed
#check @continuous_zeta_left
#check @continuousOn_zeta_horizontal
#check @norm_zeta_vertical_le
#check @norm_zeta_horizontal_le
#check @source_log_height_shift
#check @source_referenceMass_le
#check @source_horizontalLogBound_le
#check @source_horizontal_power_cost
#check @norm_horizontal_source_le
#check @transport_cost_source_le
#check @low_center_cost_source_le
#check @polynomial_left_cost_source_le
#check @norm_left_source_le
#check @zeta_psi_formula_source
#check @modulus_one_psi_formula_source
#check @principal_psi_eq_coprimePrefix
#check @principal_psi_add_badMass
#check @norm_principal_psi_sub_modulus_one_le
#check @log2_le_twice_log
#check @badMass_cost_source_le
#check @principal_psi_formula_source
#check @principal_psi_formula_values
#check @principal_character_psi_formula
#check @principal_psi_formula_regression

#print axioms zeta_psi_formula_source
#print axioms modulus_one_psi_formula_source
#print axioms principal_psi_formula_source
#print axioms principal_psi_formula_values
#print axioms principal_character_psi_formula
#print axioms principal_psi_formula_regression
