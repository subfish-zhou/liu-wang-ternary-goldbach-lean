import LiuWang.Proof.ZeroRegionFamily.Sharp.Consumer

/-! # 全部公开类型/定义与实际无零点消费者公理 -/

set_option autoImplicit false
set_option pp.fullNames true
set_option pp.universes true
set_option pp.explicit true
set_option format.width 120

namespace LiuWang.Proof.ZeroRegionFamily.Sharp

#print referenceTerm
#check @referenceTerm_antitone
#check @referenceTerm_integral
#check @reference_sum_le
#check @digamma_one_re_bound
#check @reference_shape_le
#check @digamma_one_re_le_log_max
#check @reciprocal_difference_le
#check @reciprocal_reverse_difference_le
#check @sum_shift_square_le
#check @sum_shift_square_le_two
#check @digamma_difference_hasSum
#check @digamma_shift_down_le
#check @digamma_shift_up_le
#print stechkinConductorCoeff
#check @stechkinSigma_sub_le
#check @stechkinK_ge
#check @digamma_difference_bound
#print gammaDifferenceAt
#check @gammaDifference_even
#check @gammaDifference_odd
#check @gammaDifference_le
#check @gammaDifference_le_four_fifteenths
#check @gammaDifference_low
#check @gammaDifference_high
#check @primitive_damped_bound
#check @norm_geometric_difference_le
#check @geometric_cost_nonneg
#print primeCost
#check @primePower_parameters
#check @primeCost_nonneg
#check @primeCost_eq_positive_power
#check @cpow_geometric_bound
#check @norm_factor_difference_le
#print badPrimeCost
#print principalPrimeCost
#check @norm_level_difference_le
#check @imprimitive_damped_bound
#check @norm_principal_factor_difference_le
#check @norm_principal_level_difference_le
#check @principal_damped_euler_bound
#check @principal_real_correction_eq
#check @principal_real_damped_identity
#check @xi_product
#check @xi_conj
#check @xi_reflected_order
#check @xi_reflected_multiplicity
#print xiReflect
#check @xiReflect_val
#check @xiReflect_involutive
#print xiReflection
#print xiDampedTerm
#check @xiDampedTerm_summable
#check @xiDamped_sum_nonneg
#print zetaDamped
#print poleDifference
#print shiftedGammaDifference
#check @zeta_damped_identity
#check @zeta_damped_le
#check @xi_inv_re_summable
#check @xi_inv_re_sum
#check @xi_raw_summable
#check @xi_raw_damped_nonneg
#check @zeta_damped_pole_bound
#check @real_digamma_mono
#check @real_digamma_upper
#check @real_digamma_lower
#check @stechkinSigma_bounds
#check @stechkinK_le
#check @shiftedGamma_real_bound
#check @shiftedGamma_all_height
#check @poleDifference_real_le
#check @poleDifference_high_nonpos
#check @zeta_real_strong
#check @zeta_real_function
#check @principal_real_strong
#check @principal_all_height
#check @principal_high
#check @stechkin_ratio_sigma
#check @selected_reflected_scalar
#check @selected_pair_dominates
#check @primitive_actual_selected_bound
#check @conductorCoeff_bounds
#check @badPrimeCost_le_principal
#check @principalPrimeCost_nonneg
#check @imprimitive_level_bound
#check @nonquadratic_core_function
#check @log_max_double_le
#check @nonquadratic_core
#check @log_scale_ge
#check @conductor_height_log_max_le
#check @primitive_nonquadratic_finite_gap
#check @nonquadratic_no_zero_twenty
#check @quadratic_high_core
#check @finite_gap_of_log_core
#check @primitive_high_gap
#check @nonprincipal_high_no_zero_twenty
#print primitiveZeroSum
#print zetaZeroSum
#check @primitive_full_zero_sum_bound
#check @imprimitive_full_zero_sum_bound
#check @zeta_full_zero_sum_identity
#check @principal_full_zero_sum_bound
#check @ordinary_region_twenty
#check @ordinary_zero_localized_twenty
#print axioms ordinary_region_twenty
#print axioms ordinary_zero_localized_twenty
#print axioms gammaDifference_le
#print axioms principal_real_strong
#print axioms principal_high
#print axioms imprimitive_damped_bound
#print axioms xi_inv_re_sum
#print axioms imprimitive_full_zero_sum_bound
#print axioms principal_full_zero_sum_bound

end LiuWang.Proof.ZeroRegionFamily.Sharp
