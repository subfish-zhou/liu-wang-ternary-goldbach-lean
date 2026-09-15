import LiuWang.Proof.PerronBudget.Consumer

/-! # Complete public types, actual definition values, and axiom audit -/

set_option autoImplicit false
set_option pp.universes true
set_option pp.fullNames true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.deepTerms true
set_option format.width 120

open LiuWang.Proof.PerronBudget

#check @log_two_bounds
#print axioms log_two_bounds
#check @log_four_add_four_le
#print axioms log_four_add_four_le
#check @source_series_factor
#print axioms source_series_factor
#check @source_two_rpow_le_three
#print axioms source_two_rpow_le_three
#check @source_log_bounds
#print axioms source_log_bounds
#check @source_rpow_small
#print axioms source_rpow_small
#check @source_rpow_le_nine_mul
#print axioms source_rpow_le_nine_mul
#check @million_sourceT_sq_le_endpoint
#print axioms million_sourceT_sq_le_endpoint
#check @source_cutoff_bounds
#print axioms source_cutoff_bounds
#check @source_series_factor_div_pi
#print axioms source_series_factor_div_pi
#check @closedHalfError_le
#print axioms closedHalfError_le
#check @closedHalfErrors_source_le
#print axioms closedHalfErrors_source_le
#check @heightCorrection_source_le
#print axioms heightCorrection_source_le
#check @transportCorrection_source_le
#print axioms transportCorrection_source_le
#check @log_two_source_le
#print axioms log_two_source_le
#check @closedRealEndpointError_le_stronger
#print axioms closedRealEndpointError_le_stronger
#check @closedRealEndpointError_le_source
#print axioms closedRealEndpointError_le_source
#check @sourceDomain_right_perron_paid
#print axioms sourceDomain_right_perron_paid
#check @centered_vertical_eq_actual_right
#print axioms centered_vertical_eq_actual_right
#check @source_budget_add
#print axioms source_budget_add
#check @exists_paid_estimates_all_real_endpoints
#print axioms exists_paid_estimates_all_real_endpoints
#check @psi_highZeroSum_source_all_real_endpoints
#print axioms psi_highZeroSum_source_all_real_endpoints
#check @psi_highZeroSum_source_le
#print axioms psi_highZeroSum_source_le
#check @Consumer.closed_error_original_domain
#print axioms Consumer.closed_error_original_domain
#check @Consumer.all_character_right_perron
#print axioms Consumer.all_character_right_perron
#check @Consumer.high_zero_fiber_card
#print axioms Consumer.high_zero_fiber_card
#check @Consumer.primitive_nonprincipal_psi_fixed_high_zeros
#print axioms Consumer.primitive_nonprincipal_psi_fixed_high_zeros
#check @Consumer.primitive_nonprincipal_psi_sum
#print axioms Consumer.primitive_nonprincipal_psi_sum

#print LiuWang.Proof.Interfaces.sourceL
#print LiuWang.Proof.Interfaces.sourceT
#print LiuWang.Proof.Interfaces.sourceP1
#print LiuWang.Proof.Interfaces.sourceWindowLower
#print LiuWang.Proof.ExplicitPerron.halfCutoff
#print LiuWang.Proof.ExplicitPerron.closedHalfError
#print LiuWang.Proof.ExplicitPerron.heightCorrection
#print LiuWang.Proof.ExplicitPerron.transportCorrection
#print LiuWang.Proof.ExplicitPerron.closedRealEndpointError
#print LiuWang.Proof.ExplicitPerron.psi
#print LiuWang.Proof.ExplicitPerron.centeredIntegrand
#print LiuWang.Proof.ExplicitPerron.vertical
#print LiuWang.Proof.FixedHeightZeroSum.actualRightVerticalIntegral
#print LiuWang.Proof.FixedHeightZeroSum.highZeroSum
#print LiuWang.Proof.FixedHeightZeroSum.highZeroIndices
#print LiuWang.Proof.FixedHeightZeroSum.fixedZeroIndices
#print LiuWang.Proof.Interfaces.CompletedZeroIndex
#print LiuWang.Proof.Interfaces.completedZeroValue
#print LiuWang.Proof.NonSymmetricContour.AdmissibleHeights

#check @LiuWang.Proof.ExplicitPerron.psi_eq_sum
#print axioms LiuWang.Proof.ExplicitPerron.psi_eq_sum
#check @LiuWang.Proof.ExplicitPerron.sourceDomain_right_perron
#print axioms LiuWang.Proof.ExplicitPerron.sourceDomain_right_perron
#check @LiuWang.Proof.FixedHeightZeroSum.actual_source_high_zero_estimate
#print axioms LiuWang.Proof.FixedHeightZeroSum.actual_source_high_zero_estimate
#check @LiuWang.Proof.FixedHeightZeroSum.exists_actual_high_zero_estimate_all_real_endpoints
#print axioms LiuWang.Proof.FixedHeightZeroSum.exists_actual_high_zero_estimate_all_real_endpoints
