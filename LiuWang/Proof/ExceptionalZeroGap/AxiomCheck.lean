import LiuWang.Proof.ExceptionalZeroGap.Consumer

set_option autoImplicit false
set_option pp.universes true

namespace LiuWang.Proof.ExceptionalZeroGap

#print c1
#print nearOneLower
#check @sum_range_add_fourier_completion
#check @stdAddChar_natCast_eq_charReal
#check @norm_geometric_kernel_le
#check @sum_reciprocal_min_le_harmonic
#check @harmonic_half_le_log
#check @weighted_fourier_kernel_le
#check @norm_sum_range_add_le_sqrt_mul_log
#check @norm_sum_Ico_le_sqrt_mul_log
#check @norm_sum_int_Ico_le_sqrt_mul_log
#check @sum_weighted_Ico_forward
#check @norm_sum_weighted_Ico_le
#check @antitoneOn_realLogWeight
#check @norm_sum_Ico_derivative_weight_le
#check @norm_deriv_sub_sum_floor_le
#check @sum_log_div_le_finiteHeadBudget
#check @norm_derivative_head_le_of_le
#check @norm_deriv_le_complete_head_tail_of_le
#check @norm_deriv_le_complete_head_tail
#check @log_chosen_cutoff_le
#check @chosen_head_tail_coefficient_le
#check @chosen_power_le
#check @norm_deriv_LFunction_le_source_bound
#check @norm_deriv_LFunction_le
#check @real_zero_lt_one
#check @norm_LFunction_one_le_gap_mul
#check @real_primitive_local_zero_gap
#check @derivative_interval_consumer
#check @large_conductor_local_zero_consumer
#check @EffectiveLValue.real_primitive_LFunction_one_lower

#print axioms sum_range_add_fourier_completion
#print axioms norm_geometric_kernel_le
#print axioms weighted_fourier_kernel_le
#print axioms norm_sum_int_Ico_le_sqrt_mul_log
#print axioms norm_sum_weighted_Ico_le
#print axioms antitoneOn_realLogWeight
#print axioms norm_deriv_sub_sum_floor_le
#print axioms sum_log_div_le_finiteHeadBudget
#print axioms norm_deriv_le_complete_head_tail_of_le
#print axioms norm_deriv_le_complete_head_tail
#print axioms log_chosen_cutoff_le
#print axioms chosen_head_tail_coefficient_le
#print axioms chosen_power_le
#print axioms norm_deriv_LFunction_le_source_bound
#print axioms norm_deriv_LFunction_le
#print axioms real_zero_lt_one
#print axioms norm_LFunction_one_le_gap_mul
#print axioms real_primitive_local_zero_gap
#print axioms derivative_interval_consumer
#print axioms large_conductor_local_zero_consumer
#print axioms EffectiveLValue.real_primitive_LFunction_one_lower

end LiuWang.Proof.ExceptionalZeroGap
