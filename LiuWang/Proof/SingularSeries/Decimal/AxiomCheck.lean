import LiuWang.Proof.SingularSeries.Decimal.Consumer

set_option pp.fullNames true
set_option pp.universes true
set_option pp.funBinderTypes true

open LiuWang.Proof.SingularSeries.Decimal

#print a
#print b
set_option pp.proofs true in
#print squareReciprocal
#print oddPrimes
#print smallRatio
#print LiuWang.Proof.SingularSeries.universalProduct
#print LiuWang.Proof.SingularSeries.universalTruncated
#print LiuWang.Proof.SingularSeries.coefficient
#print LiuWang.Proof.SingularSeries.series
#print LiuWang.Proof.SingularSeries.I11
#print LiuWang.Proof.SingularSeries.fullMass
#print LiuWang.Proof.Interfaces.sourceP
#print LiuWang.Proof.Interfaces.deltaRadius

#check @b_pos
#check @b_le_one
#check @a_pos
#check @local_comparison
#check @odd_cube_step
#check @odd_cube_interval
#check @odd_cube_finite
#check @odd_tail_finite
#check @one_sub_sum_le_prod
#check @prime_correction_lower
#check @squareReciprocal_summable
#check @finite_zeta_inverse_upper
#check @finite_zeta_product_lower
#check @mem_oddPrimes
#check @universalTruncated_eq
#check @prime_filter_split
#check @odd_zeta_product_lower
#check @odd_b_product_pos
#check @odd_a_product_pos
#check @smallRatio_pos
#check @odd_product_split
#check @smallRatio_mul_odd_b
#check @cubic_correction_nonneg
#check @truncated_comparison
#check @universalProduct_analytic_lower_bound
#check @oddPrimes_hundred
#check @fixed_kernel
#check @pi_comparison
#check @universalProduct_decimal
#check @series_decimal_lower_bound
#check @re_I11_decimal_lower_bound
#check @hasSum_zeta_two
#check @EulerProduct.prod_filter_prime_geometric_eq_tsum_factoredNumbers
#check @Real.pi_lt_d6
#check @LiuWang.Proof.SingularSeries.Uniform.re_I11_of_universal_decimal
#check @LiuWang.Proof.SingularIntegral.integral_J_cube

#print axioms a
#print axioms b
#print axioms b_pos
#print axioms b_le_one
#print axioms a_pos
#print axioms local_comparison
#print axioms odd_cube_step
#print axioms odd_cube_interval
#print axioms odd_cube_finite
#print axioms odd_tail_finite
#print axioms one_sub_sum_le_prod
#print axioms prime_correction_lower
#print axioms squareReciprocal
#print axioms squareReciprocal_summable
#print axioms finite_zeta_inverse_upper
#print axioms finite_zeta_product_lower
#print axioms oddPrimes
#print axioms mem_oddPrimes
#print axioms universalTruncated_eq
#print axioms prime_filter_split
#print axioms odd_zeta_product_lower
#print axioms smallRatio
#print axioms odd_b_product_pos
#print axioms odd_a_product_pos
#print axioms smallRatio_pos
#print axioms odd_product_split
#print axioms smallRatio_mul_odd_b
#print axioms cubic_correction_nonneg
#print axioms truncated_comparison
#print axioms universalProduct_analytic_lower_bound
#print axioms oddPrimes_hundred
#print axioms fixed_kernel
#print axioms pi_comparison
#print axioms universalProduct_decimal
#print axioms series_decimal_lower_bound
#print axioms re_I11_decimal_lower_bound

run_cmd do
  let env ← Lean.getEnv
  let paths : List (List Lean.Name) := [
    [``re_I11_decimal_lower_bound, ``universalProduct_decimal,
      ``universalProduct_analytic_lower_bound, ``truncated_comparison,
      ``prime_correction_lower, ``odd_tail_finite, ``odd_cube_finite,
      ``odd_cube_interval, ``odd_cube_step],
    [``universalProduct_analytic_lower_bound, ``truncated_comparison, ``local_comparison],
    [``universalProduct_decimal, ``universalProduct_analytic_lower_bound,
      ``odd_zeta_product_lower, ``finite_zeta_product_lower, ``finite_zeta_inverse_upper,
      ``EulerProduct.prod_filter_prime_geometric_eq_tsum_factoredNumbers],
    [``finite_zeta_inverse_upper, ``squareReciprocal_summable, ``hasSum_zeta_two],
    [``universalProduct_decimal, ``fixed_kernel, ``oddPrimes_hundred],
    [``universalProduct_decimal, ``pi_comparison, ``Real.pi_lt_d6],
    [``re_I11_decimal_lower_bound,
      ``LiuWang.Proof.SingularSeries.Uniform.re_I11_of_universal_decimal,
      ``LiuWang.Proof.SingularSeries.Uniform.re_I11_only_universal_product,
      ``LiuWang.Proof.SingularSeries.re_I11_uniform_lower_bound,
      ``LiuWang.Proof.SingularSeries.re_I11_lower_bound,
      ``LiuWang.Proof.SingularSeries.I11_eq_series_main_sub_errors,
      ``LiuWang.Proof.SingularSeries.I11_eq_partial_main_sub_arcError,
      ``LiuWang.Proof.SingularSeries.integral_cube_eq_fullMass,
      ``LiuWang.Proof.SingularIntegral.integral_J_cube],
    [``series_decimal_lower_bound, ``LiuWang.Proof.SingularSeries.two_mul_universalProduct_le_series],
    [``universalProduct_analytic_lower_bound, ``truncated_comparison,
      ``universalTruncated_eq, ``LiuWang.Proof.SingularSeries.universalTruncated_source],
    [``truncated_comparison, ``prime_correction_lower, ``one_sub_sum_le_prod]]
  for path in paths do
    for (src, dst) in path.zip path.tail do
      let some info := env.find? src | throwError "Missing declaration {src}"
      let some value := info.value? (allowOpaque := true) | throwError "Missing value {src}"
      unless value.getUsedConstants.contains dst do
        throwError "Missing direct value dependency {src} -> {dst}"
    Lean.logInfo m!"VALUE_PATH_OK {path}"
