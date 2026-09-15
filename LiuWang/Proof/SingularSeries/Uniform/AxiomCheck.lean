import LiuWang.Proof.SingularSeries.Uniform.Consumer

set_option pp.fullNames true
set_option pp.universes true
set_option pp.funBinderTypes true

open LiuWang.Proof.SingularSeries.Uniform

#print squareSum
#print tau
#print ratioSquare
#print majorant
#print comparisonSequence
#print LiuWang.Proof.SingularSeries.coefficient
#print LiuWang.Proof.SingularSeries.denominators
#print LiuWang.Proof.SingularSeries.absoluteTail
#print LiuWang.Proof.SingularSeries.coefficientTail
#print LiuWang.Proof.SingularSeries.weightedTotientSum
#print LiuWang.Proof.SingularSeries.I11
#print LiuWang.Proof.SingularSeries.universalProduct
#print LiuWang.Proof.SingularSeries.universalTruncated
#print LiuWang.Proof.Interfaces.sourceP
#print LiuWang.Proof.Interfaces.sourceL
#print LiuWang.Proof.Interfaces.deltaRadius

#check @sum_multiples
#check @sum_divisors_reindex
#check @squareSum_nonneg
#check @convolution_nonneg
#check @squareSum_convolution_le
#check @sum_divisor_quotient_le
#check @reciprocal_square_step
#check @reciprocal_square_tail
#check @reciprocal_square_tail_le
#check @reciprocal_square_prefix
#check @reciprocal_square_sixth_constant
#check @tau_multiplicative
#check @tau_one
#check @zeta_real_apply
#check @tau_nonneg
#check @convolution_prime
#check @tau_prime
#check @squareSum_zeta_le
#check @squareSum_tau_le
#check @squareSum_tau_six_lt
#check @ratioSquare_nonneg
#check @ratioSquare_mul
#check @ratioSquare_prime_power
#check @ratioSquare_prime_le
#check @majorant_apply
#check @majorant_nonneg
#check @majorant_multiplicative
#check @majorant_prime_power_lower
#check @ratioSquare_le_majorant
#check @ratioSquare_sum_le
#check @ratioSquare_sum_real_le
#check @weightedTotientSum_le
#check @finite_abel
#check @weighted_sum_le_of_prefix_le
#check @comparisonSequence_sum
#check @comparisonSequence_weighted_sum
#check @reciprocal_weight_antitone
#check @ratioSquare_weighted_tail_finite
#check @inverse_totient_sq_eq_weighted_ratio
#check @inverse_totient_tail_finite
#check @strict_tail_index_iff
#check @inverse_totient_strict_tail_finite
#check @inverse_totient_strict_tail_summable
#check @inverse_totient_strict_tail_le
#check @absoluteTail_summable
#check @absoluteTail_le
#check @coefficientTail_le
#check @sourceP_lower
#check @sourceP_ge_one
#check @source_weightedTotientSum_le
#check @source_absoluteTail_le
#check @source_coefficientTail_le
#check @source_partialSeries_error_le
#check @source_weighted_arc_expression_le
#check @source_arcError_le
#check @re_I11_arithmetic_errors_paid
#check @re_I11_only_universal_product
#check @decimal_margin
#check @re_I11_of_universal_decimal
#check @re_I11_of_finite_certificate
#check @LiuWang.Proof.SingularSeries.universal_decimal_of_finite_certificate
#check @LiuWang.Proof.SingularIntegral.integral_J_cube

#print axioms sum_multiples
#print axioms sum_divisors_reindex
#print axioms squareSum
#print axioms squareSum_nonneg
#print axioms convolution_nonneg
#print axioms squareSum_convolution_le
#print axioms sum_divisor_quotient_le
#print axioms reciprocal_square_step
#print axioms reciprocal_square_tail
#print axioms reciprocal_square_tail_le
#print axioms reciprocal_square_prefix
#print axioms reciprocal_square_sixth_constant
#print axioms tau
#print axioms tau_multiplicative
#print axioms tau_one
#print axioms zeta_real_apply
#print axioms tau_nonneg
#print axioms convolution_prime
#print axioms tau_prime
#print axioms squareSum_zeta_le
#print axioms squareSum_tau_le
#print axioms squareSum_tau_six_lt
#print axioms ratioSquare
#print axioms ratioSquare_nonneg
#print axioms ratioSquare_mul
#print axioms ratioSquare_prime_power
#print axioms ratioSquare_prime_le
#print axioms majorant
#print axioms majorant_apply
#print axioms majorant_nonneg
#print axioms majorant_multiplicative
#print axioms majorant_prime_power_lower
#print axioms ratioSquare_le_majorant
#print axioms ratioSquare_sum_le
#print axioms ratioSquare_sum_real_le
#print axioms weightedTotientSum_le
#print axioms finite_abel
#print axioms weighted_sum_le_of_prefix_le
#print axioms comparisonSequence
#print axioms comparisonSequence_sum
#print axioms comparisonSequence_weighted_sum
#print axioms reciprocal_weight_antitone
#print axioms ratioSquare_weighted_tail_finite
#print axioms inverse_totient_sq_eq_weighted_ratio
#print axioms inverse_totient_tail_finite
#print axioms strict_tail_index_iff
#print axioms inverse_totient_strict_tail_finite
#print axioms inverse_totient_strict_tail_summable
#print axioms inverse_totient_strict_tail_le
#print axioms absoluteTail_summable
#print axioms absoluteTail_le
#print axioms coefficientTail_le
#print axioms sourceP_lower
#print axioms sourceP_ge_one
#print axioms source_weightedTotientSum_le
#print axioms source_absoluteTail_le
#print axioms source_coefficientTail_le
#print axioms source_partialSeries_error_le
#print axioms source_weighted_arc_expression_le
#print axioms source_arcError_le
#print axioms re_I11_arithmetic_errors_paid
#print axioms re_I11_only_universal_product
#print axioms decimal_margin
#print axioms re_I11_of_universal_decimal
#print axioms re_I11_of_finite_certificate

run_cmd do
  let env ← Lean.getEnv
  let paths : List (List Lean.Name) := [
    [``re_I11_of_finite_certificate, ``re_I11_of_universal_decimal,
      ``re_I11_only_universal_product,
      ``LiuWang.Proof.SingularSeries.re_I11_uniform_lower_bound,
      ``LiuWang.Proof.SingularSeries.re_I11_lower_bound,
      ``LiuWang.Proof.SingularSeries.I11_eq_series_main_sub_errors,
      ``LiuWang.Proof.SingularSeries.I11_eq_partial_main_sub_arcError,
      ``LiuWang.Proof.SingularSeries.integral_cube_eq_fullMass,
      ``LiuWang.Proof.SingularIntegral.integral_J_cube],
    [``re_I11_only_universal_product, ``source_absoluteTail_le, ``absoluteTail_le,
      ``inverse_totient_strict_tail_le, ``inverse_totient_strict_tail_summable,
      ``inverse_totient_strict_tail_finite, ``inverse_totient_tail_finite,
      ``ratioSquare_weighted_tail_finite, ``ratioSquare_sum_le,
      ``squareSum_tau_six_lt, ``squareSum_tau_le, ``squareSum_convolution_le],
    [``re_I11_only_universal_product, ``source_weighted_arc_expression_le,
      ``source_weightedTotientSum_le, ``weightedTotientSum_le,
      ``ratioSquare_sum_real_le, ``ratioSquare_sum_le, ``ratioSquare_le_majorant,
      ``majorant_prime_power_lower, ``tau_prime],
    [``re_I11_of_finite_certificate,
      ``LiuWang.Proof.SingularSeries.universal_decimal_of_finite_certificate,
      ``LiuWang.Proof.SingularSeries.universalProduct_finite_lower_bound]]
  for path in paths do
    for (src, dst) in path.zip path.tail do
      let some info := env.find? src | throwError "Missing declaration {src}"
      let some value := info.value? (allowOpaque := true) | throwError "Missing value {src}"
      unless value.getUsedConstants.contains dst do
        throwError "Missing direct value dependency {src} -> {dst}"
    Lean.logInfo m!"VALUE_PATH_OK {path}"
