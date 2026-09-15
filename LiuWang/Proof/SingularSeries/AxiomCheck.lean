import LiuWang.Proof.SingularSeries.Consumer

set_option pp.fullNames true
set_option pp.universes true
set_option pp.funBinderTypes true

open LiuWang.Proof.SingularSeries

#print reducedResidues
#print ramanujan
#print coefficient
#print divisorWeight
#print ramanujanArithmetic
#print parityFactor
#print divisorMass
#print realCoefficient
#print localFactor
#print series
#print cubeIntegrand
#print denominators
#print partialSeries
#print coefficientTail
#print absoluteTail
#print I11
#print fullMass
#print arcError
#print weightedTotientSum
#print universalProduct
#print universalTruncated
#print primeFactor
#print adjustedUniversal
#print AnalyticNumberTheory.LargeSieve.charReal
#print ArithmeticFunction.moebius
#print Nat.totient
#print LiuWang.Proof.Interfaces.J
#print LiuWang.Proof.Interfaces.Jrho
#print LiuWang.Proof.Interfaces.sourceP
#print LiuWang.Proof.Interfaces.sourceL
#print LiuWang.Proof.Interfaces.deltaRadius
#print MathlibNt.SieveTheory.SingularSeries.liuUniversalProduct
#print MathlibNt.SieveTheory.SingularSeries.liuUniversalProductTruncated
#print MathlibNt.SieveTheory.SingularSeries.liuBaseDeviation

#check @coefficient_source
#check @ramanujan_zero
#check @coefficient_zero
#check @reducedResidues_card
#check @stdAddChar_negative_phase
#check @sum_Icc_eq_sum_range_of_endpoint
#check @ramanujan_eq_zmod
#check @ramanujan_one
#check @coefficient_one
#check @ramanujan_conj
#check @ramanujan_im
#check @ramanujan_eq_real
#check @coefficient_eq_real
#check @coefficient_eq_zero_of_not_squarefree
#check @norm_ramanujan_le_totient
#check @norm_coefficient_le
#check @ramanujan_prime
#check @coefficient_prime
#check @coefficient_prime_power
#check @coefficient_two_of_odd
#check @sum_zmod_eq_sum_range
#check @complete_phase_sum
#check @sum_Icc_dvd
#check @phase_sum_on_multiples
#check @divisorWeight_apply
#check @divisorWeight_multiplicative
#check @ramanujanArithmetic_multiplicative
#check @ramanujan_integer_formula
#check @ramanujan_eq_arithmetic
#check @ramanujan_integral
#check @ramanujan_mul
#check @coefficient_mul
#check @parityFactor_mul
#check @parityFactor_pow
#check @prime_le_parityFactor_mul_sub_sq
#check @le_parityFactor_mul_totient_sq
#check @le_two_mul_totient_sq
#check @divisorMass_nonneg
#check @norm_moebius_complex_le
#check @ramanujan_integer_formula'
#check @norm_ramanujan_le_divisorMass
#check @inv_totient_cube_le
#check @norm_coefficient_le_fixed_majorant
#check @coefficient_norm_summable
#check @coefficient_summable
#check @ofReal_realCoefficient
#check @realCoefficient_zero
#check @realCoefficient_one
#check @realCoefficient_mul
#check @realCoefficient_norm_summable
#check @realCoefficient_summable
#check @localFactor_eq_one_add
#check @realCoefficient_prime_power
#check @localFactor_eq_prime_power_sum
#check @ofReal_series
#check @euler_hasProd
#check @series_eq_eulerProduct
#check @original_series_eq_eulerProduct
#check @localFactor_two_of_odd
#check @localFactor_pos_of_odd
#check @series_pos_of_odd
#check @weightMass_one
#check @weightVariation_one
#check @J_norm_le_length
#check @J_abs_mul_norm_le
#check @J_norm_le_reciprocal
#check @J_norm_le_min
#check @J_zero
#check @cubeIntegrand_integrable
#check @cubeIntegrand_norm_le
#check @norm_integral_Ioi_le_inv_cube
#check @integral_sub_interval_eq_tails
#check @cube_integral_tail_bound
#check @cube_integral_truncation
#check @mem_denominators
#check @coefficientTail_norm_le
#check @partialSeries_add_tail
#check @partialSeries_error_le
#check @I11_source
#check @fullMass_nonneg
#check @integral_cube_eq_fullMass
#check @I11_eq_partial_main_sub_arcError
#check @norm_coefficient_le_moebius
#check @weightedTotientSum_nonneg
#check @delta_tail_identity
#check @source_arc_constant_le
#check @arcError_bound
#check @I11_eq_series_main_sub_errors
#check @re_I11_lower_bound
#check @universalProduct_source
#check @universalTruncated_source
#check @universalProduct_pos
#check @universalTruncated_pos
#check @primeFactor_hasProd
#check @primeFactor_lower
#check @two_mul_universalProduct_le_series
#check @all_integer_factor_le_universalFactor
#check @adjustedUniversal_step
#check @adjustedUniversal_le_truncated
#check @universalProduct_finite_lower_bound
#check @universal_decimal_of_finite_certificate
#check @re_I11_uniform_lower_bound
#check @source_absolute_convergence
#check @source_euler_identity
#check @source_positive_lower_bound
#check @source_radius_integral_truncation
#check @LiuWang.Proof.SingularIntegral.integral_J_cube
#check @LiuWang.Proof.SingularIntegral.Jrho_norm_le_mass
#check @LiuWang.Proof.SingularIntegral.Jrho_abs_mul_norm_le_variation

#print axioms reducedResidues
#print axioms ramanujan
#print axioms coefficient
#print axioms coefficient_source
#print axioms ramanujan_zero
#print axioms coefficient_zero
#print axioms reducedResidues_card
#print axioms stdAddChar_negative_phase
#print axioms sum_Icc_eq_sum_range_of_endpoint
#print axioms ramanujan_eq_zmod
#print axioms ramanujan_one
#print axioms coefficient_one
#print axioms ramanujan_conj
#print axioms ramanujan_im
#print axioms ramanujan_eq_real
#print axioms coefficient_eq_real
#print axioms coefficient_eq_zero_of_not_squarefree
#print axioms norm_ramanujan_le_totient
#print axioms norm_coefficient_le
#print axioms ramanujan_prime
#print axioms coefficient_prime
#print axioms coefficient_prime_power
#print axioms coefficient_two_of_odd
#print axioms sum_zmod_eq_sum_range
#print axioms complete_phase_sum
#print axioms sum_Icc_dvd
#print axioms phase_sum_on_multiples
#print axioms divisorWeight
#print axioms divisorWeight_apply
#print axioms divisorWeight_multiplicative
#print axioms ramanujanArithmetic
#print axioms ramanujanArithmetic_multiplicative
#print axioms ramanujan_integer_formula
#print axioms ramanujan_eq_arithmetic
#print axioms ramanujan_integral
#print axioms ramanujan_mul
#print axioms coefficient_mul
#print axioms parityFactor
#print axioms parityFactor_mul
#print axioms parityFactor_pow
#print axioms prime_le_parityFactor_mul_sub_sq
#print axioms le_parityFactor_mul_totient_sq
#print axioms le_two_mul_totient_sq
#print axioms divisorMass
#print axioms divisorMass_nonneg
#print axioms norm_moebius_complex_le
#print axioms ramanujan_integer_formula'
#print axioms norm_ramanujan_le_divisorMass
#print axioms inv_totient_cube_le
#print axioms norm_coefficient_le_fixed_majorant
#print axioms coefficient_norm_summable
#print axioms coefficient_summable
#print axioms realCoefficient
#print axioms ofReal_realCoefficient
#print axioms realCoefficient_zero
#print axioms realCoefficient_one
#print axioms realCoefficient_mul
#print axioms realCoefficient_norm_summable
#print axioms realCoefficient_summable
#print axioms localFactor
#print axioms localFactor_eq_one_add
#print axioms realCoefficient_prime_power
#print axioms localFactor_eq_prime_power_sum
#print axioms series
#print axioms ofReal_series
#print axioms euler_hasProd
#print axioms series_eq_eulerProduct
#print axioms original_series_eq_eulerProduct
#print axioms localFactor_two_of_odd
#print axioms localFactor_pos_of_odd
#print axioms series_pos_of_odd
#print axioms weightMass_one
#print axioms weightVariation_one
#print axioms J_norm_le_length
#print axioms J_abs_mul_norm_le
#print axioms J_norm_le_reciprocal
#print axioms J_norm_le_min
#print axioms J_zero
#print axioms cubeIntegrand
#print axioms cubeIntegrand_integrable
#print axioms cubeIntegrand_norm_le
#print axioms norm_integral_Ioi_le_inv_cube
#print axioms integral_sub_interval_eq_tails
#print axioms cube_integral_tail_bound
#print axioms cube_integral_truncation
#print axioms denominators
#print axioms mem_denominators
#print axioms partialSeries
#print axioms coefficientTail
#print axioms absoluteTail
#print axioms coefficientTail_norm_le
#print axioms partialSeries_add_tail
#print axioms partialSeries_error_le
#print axioms I11
#print axioms I11_source
#print axioms fullMass
#print axioms fullMass_nonneg
#print axioms integral_cube_eq_fullMass
#print axioms arcError
#print axioms I11_eq_partial_main_sub_arcError
#print axioms norm_coefficient_le_moebius
#print axioms weightedTotientSum
#print axioms weightedTotientSum_nonneg
#print axioms delta_tail_identity
#print axioms source_arc_constant_le
#print axioms arcError_bound
#print axioms I11_eq_series_main_sub_errors
#print axioms re_I11_lower_bound
#print axioms universalProduct
#print axioms universalTruncated
#print axioms universalProduct_source
#print axioms universalTruncated_source
#print axioms universalProduct_pos
#print axioms universalTruncated_pos
#print axioms primeFactor
#print axioms primeFactor_hasProd
#print axioms primeFactor_lower
#print axioms two_mul_universalProduct_le_series
#print axioms all_integer_factor_le_universalFactor
#print axioms adjustedUniversal
#print axioms adjustedUniversal_step
#print axioms adjustedUniversal_le_truncated
#print axioms universalProduct_finite_lower_bound
#print axioms universal_decimal_of_finite_certificate
#print axioms re_I11_uniform_lower_bound
#print axioms source_absolute_convergence
#print axioms source_euler_identity
#print axioms source_positive_lower_bound
#print axioms source_radius_integral_truncation
#print axioms LiuWang.Proof.SingularIntegral.integral_J_cube
#print axioms LiuWang.Proof.SingularIntegral.Jrho_norm_le_mass
#print axioms LiuWang.Proof.SingularIntegral.Jrho_abs_mul_norm_le_variation
