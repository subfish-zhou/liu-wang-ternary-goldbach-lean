import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524.Consumer

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524

theorem originalBracket_literal (L x : ℝ) :
    originalBracket L x =
      (1.8771 * L ^ (1 - 9 * x / 20) *
        (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (L ^ x)) +
          2.50637 / Real.log (Real.log (L ^ x))) * (x * Real.log L) ^ (1 / 15 : ℝ) *
        (254231 / Real.log (10000 * L ^ x * Real.log (L ^ x)) + 17102) *
          Real.log (10000 * L ^ x * Real.log (L ^ x)) ^ 6 +
      1.0159 * 16541 * L ^ (1 - x / 2) *
        (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (L ^ x)) +
          2.50637 / Real.log (Real.log (L ^ x))) * Real.log (10000 * x * Real.log L) ^ 6) *
      Real.exp (-0.478 * L / Real.log (10000 * Real.pi * L ^ x)) := rfl

#check @originalBracket
#print axioms originalBracket
#check @logNu
#print axioms logNu
#check @heightLog
#print axioms heightLog
#check @densityLog
#print axioms densityLog
#check @logBracket
#print axioms logBracket
#check @originalBracket_eq_logBracket
#print axioms originalBracket_eq_logBracket
#check @modulus_parameter
#print axioms modulus_parameter
#check @modulus_logBracket
#print axioms modulus_logBracket
#check @log_s_ge_three
#print axioms log_s_ge_three
#check @logNu_bounds
#print axioms logNu_bounds
#check @logarithm_scaling
#print axioms logarithm_scaling
#check @logNu_scaling
#print axioms logNu_scaling
#check @heightLog_bounds
#print axioms heightLog_bounds
#check @heightLog_scaling
#print axioms heightLog_scaling
#check @real_parameter_scaling
#print axioms real_parameter_scaling
#check @common_exponential_scaling
#print axioms common_exponential_scaling
#check @small_power_scaling
#print axioms small_power_scaling
#check @density_coefficient_scaling
#print axioms density_coefficient_scaling
#check @first_amplitude_scaling
#print axioms first_amplitude_scaling
#check @second_amplitude_scaling
#print axioms second_amplitude_scaling
#check @originalBracket_reduce_L
#print axioms originalBracket_reduce_L
#check @log_thousand_lower
#print axioms log_thousand_lower
#check @original_low_coefficient
#print axioms original_low_coefficient
#check @original_power_constant
#print axioms original_power_constant
#check @original_decimal_coefficients
#print axioms original_decimal_coefficients
#check @logarithm_correction_nonneg
#print axioms logarithm_correction_nonneg
#check @euler_corrected_harmonic_upper
#print axioms euler_corrected_harmonic_upper
#check @euler_upper
#print axioms euler_upper
#check @exp_euler_upper
#print axioms exp_euler_upper
#check @exp_nat_add_upper
#print axioms exp_nat_add_upper
#check @exp_nat_add_lower
#print axioms exp_nat_add_lower
#check @log_3100_precise
#print axioms log_3100_precise
#check @log_48_precise
#print axioms log_48_precise
#check @original_height_precise
#print axioms original_height_precise
#check @endpoint_logs
#print axioms endpoint_logs
#check @endpoint_power
#print axioms endpoint_power
#check @endpoint_nu
#print axioms endpoint_nu
#check @endpoint_exponent
#print axioms endpoint_exponent
#check @endpoint_rational_certificate
#print axioms endpoint_rational_certificate
#check @firstPart
#print axioms firstPart
#check @logNu_monotone
#print axioms logNu_monotone
#check @densityKernel_monotone
#print axioms densityKernel_monotone
#check @firstPart_monotone
#print axioms firstPart_monotone
#check @secondPart
#print axioms secondPart
#check @original_two_parts
#print axioms original_two_parts
#check @firstPart_endpoint
#print axioms firstPart_endpoint
#check @secondPart_exponent
#print axioms secondPart_exponent
#check @secondPart_rational_certificate
#print axioms secondPart_rational_certificate
#check @secondPart_paid
#print axioms secondPart_paid
#check @logBracket_base_paid
#print axioms logBracket_base_paid
#check @originalBracket_paid
#print axioms originalBracket_paid
#check @modulus_bracket_paid
#print axioms modulus_bracket_paid
#check @frozenDensity
#print axioms frozenDensity
#check @densityLog_modulus
#print axioms densityLog_modulus
#check @original_density_frozen
#print axioms original_density_frozen
#check @frozenDensity_nonneg
#print axioms frozenDensity_nonneg
#check @original_frozen_integral
#print axioms original_frozen_integral
#check @original_modulus_power
#print axioms original_modulus_power
#check @sqrt_totient_original
#print axioms sqrt_totient_original
#check @original_frozen_weight
#print axioms original_frozen_weight
#check @lowDensityBill_le_originalBracket
#print axioms lowDensityBill_le_originalBracket
#check @equation_5_24_original_bill
#print axioms equation_5_24_original_bill
#check @equation_5_24_original_contribution
#print axioms equation_5_24_original_contribution
#check @originalBracket_literal
#print axioms originalBracket_literal

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524
