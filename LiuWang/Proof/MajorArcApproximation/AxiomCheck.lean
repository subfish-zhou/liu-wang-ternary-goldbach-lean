import LiuWang.Proof.MajorArcApproximation.Consumer

/-! # 实际主弧三次近似：公开定义、完整类型和标准公理 -/

set_option format.width 120
set_option pp.universes true

open LiuWang.Proof.MajorArcApproximation

#print model
#print cubicCost
#print arcPhase
#print numerators
#print coreIndices
#print totalLength
#print majorIntegral
#print modelIntegral
#print epsilon
#print uniformError
#print errorIntegral
#print packet
#print interactionKernel
#print interactionIntegral
#print pureIntegral

#check @model_eq
#check @continuous_J
#check @continuous_zeroPacket
#check @continuous_model
#check @norm_S_le_psi
#check @norm_S_le_seven
#check @norm_S_sub_model
#check @norm_cube_sub_le
#check @cubicCost_nonneg
#check @cubicCost_mono
#check @continuous_arcPhase
#check @norm_arcPhase
#check @model_cube_integrable
#check @mem_numerators
#check @mem_coreIndices
#check @M1_eq_core_union
#check @core_pairwise_disjoint
#check @integral_M1_eq_sum
#check @delta_le
#check @totalLength_le
#check @majorIntegral_eq_sum
#check @epsilon_eq
#check @continuous_epsilon
#check @epsilon_nonneg
#check @principalMass_le_one
#check @nonprincipalMass_le_q
#check @epsilon_le_core
#check @uniformError_nonneg
#check @uniformError_le_N
#check @continuous_cubicCost_epsilon
#check @arc_error_integrable
#check @major_sub_model_eq
#check @norm_major_sub_model_le_errorIntegral
#check @errorIntegral_le_uniform
#check @uniform_cubicCost_le
#check @errorIntegral_le_log_power
#check @norm_major_sub_model_le_log_power
#check @log_power_le_decimal
#check @norm_major_sub_model_le_decimal
#check @packet_eq
#check @model_eq_main_sub_packet
#check @continuous_packet
#check @continuous_interactionKernel
#check @interaction_integrable
#check @cube_model_eq
#check @arcPhase_split
#check @principalCoefficient_cube
#check @pure_kernel_eq
#check @pureIntegral_eq_I11
#check @modelIntegral_eq_I11_add_interaction
#check @norm_major_sub_I11_interaction
#check @re_major_lower_mother
#check @re_major_lower_log_power
#check @re_major_lower_analytic
#check @re_major_lower_strong
#check @packet_eq_values
#check @packet_closed_window
#check @model_eq_values
#check @model_one
#check @core_strong_error
#check @major_arc_approximation
#check @major_arc_with_signed_zeros
#check @major_arc_with_signed_zeros_decimal
#check @major_arc_re_strong

#print axioms norm_S_sub_model
#print axioms norm_S_le_psi
#print axioms continuous_model
#print axioms integral_M1_eq_sum
#print axioms epsilon_le_core
#print axioms norm_major_sub_model_le_errorIntegral
#print axioms norm_major_sub_model_le_log_power
#print axioms norm_major_sub_model_le_decimal
#print axioms pureIntegral_eq_I11
#print axioms modelIntegral_eq_I11_add_interaction
#print axioms packet_eq_values
#print axioms packet_closed_window
#print axioms major_arc_approximation
#print axioms major_arc_with_signed_zeros
#print axioms major_arc_with_signed_zeros_decimal
#print axioms re_major_lower_analytic
#print axioms major_arc_re_strong
