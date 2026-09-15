import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OrdinaryPayment

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart

#print axioms sourceDensity
#print axioms integral_exp_affine
#print axioms integral_density_exponential
#print axioms density_power_envelope
#print axioms sourceDensity_continuous
#print axioms lowHeight_log_bounds
#print axioms log_ten_le
#print axioms enlarged_height_logs
#print axioms M3_density_logs
#print axioms density_amgm
#print axioms sixth_power_tangent
#print axioms density_sqrt_decay
#print axioms density_coupled_decay
#print axioms density_endpoint_certificate
#print axioms exp_density_shift_le
#print axioms integrated_density_envelope
#print axioms source_density_integral_bound
#print axioms lowDensityBill
#print axioms density_scalar_paid
#print axioms equation_5_24_explicit
#print axioms enlarged_height_source_domain
#print axioms low_count_integral_le_densityBill
#print axioms exceptionalTailBill
#print axioms sigma4_three_source_pieces_paid
#print axioms highEndpointDensity
#print axioms high_endpoint_rpow_certificate
#print axioms high_endpoint_rpow_global
#print axioms high_endpoint_density_global
#print axioms high_endpoint_price_certificate
#print axioms high_endpoint_scalar_paid
#print axioms high_endpoint_density_envelope
#print axioms high_endpoint_source_domain
#print axioms countIntegral_le_left_count
#print axioms equation_5_41_explicit
#print axioms equation_5_41_actual_count
#print axioms high_count_reduction_endpoint_paid
#print axioms sixth_power_decay
#print axioms middle_base_factor
#print axioms middle_height_log_global
#print axioms middle_power_global
#print axioms lower_beta_endpoint_prices
#print axioms equation_5_30_scalar
#print axioms high_lower_beta_scalar
#print axioms lower_beta_integral_identity
#print axioms equation_5_30_integral
#print axioms equation_5_40_low_integral
#print axioms ordinary_height_logs
#print axioms ordinary_gamma_bound
#print axioms ordinary_horizontal_bound
#print axioms ordinary_scalar_absorption
#print axioms ordinary_uniform_nonprincipal
#print axioms ordinary_uniform_principal
#print axioms ordinary_count_character
#print axioms ordinary_count_family
#print axioms ordinary_band_linear
#print axioms ordinary_half_band
#print axioms ordinary_inverse_band
#print axioms original_middle_ordinary_band
#print axioms original_high_ordinary_band
#print axioms scaled_low_beta_le
#print axioms sigma5_low_beta_paid
#print axioms sigma6_low_beta_paid
#print axioms equation_5_31_actual_count
#print axioms sigma6_low_and_endpoint_paid
#print axioms S_four_new_payments

#check @equation_5_24_explicit
#check @sigma4_three_source_pieces_paid
#check @equation_5_41_actual_count
#check @sigma5_low_beta_paid
#check @sigma6_low_beta_paid
#check @sigma6_low_and_endpoint_paid
#check @S_four_new_payments

example {q : ℕ} [NeZero q] {X y a : ℝ} :
    countIntegral q X y a a = 0 := by
  simp only [countIntegral, intervalIntegral.integral_same]

example {X : ℝ} (hX : 0 < X) :
    X ^ (-1 / 2 : ℝ) +
      (∫ alpha in (1 / 2 : ℝ)..(59 / 60), betaKernel X alpha) = X ^ (-1 / 60 : ℝ) :=
  lower_beta_integral_identity hX

example {q : ℕ} [NeZero q] {alpha : ℝ} (ha : 0 ≤ alpha) :
    (LiuWang.Proof.DirichletZeroCount.familyCount q alpha lowHeight : ℝ) ≤
      q.totient * (lowHeight / 3) * Real.log ((q : ℝ) * lowHeight) :=
  ordinary_count_family q ha le_rfl

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart
