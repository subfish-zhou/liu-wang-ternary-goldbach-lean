import LiuWang.Proof.PerronRecovery.Consumer

/-! Public contracts and axiom cones of the recovered chain. -/

set_option autoImplicit false
set_option pp.universes true

open LiuWang.Proof.PerronRecovery

#check @seriesBound
#check @seriesBound_nonneg
#check @mangoldt_normSum_le
#check @normSum_twisted_le
#check @norm_logDeriv_le
#check @source_abscissa_mem
#check @seriesBound_source
#check @truncationError
#check @heightError
#check @endpointError
#check @actualError
#check @normSum_twisted_le_of_majorant
#check @norm_logDeriv_le_of_majorant
#check @norm_character_perron_le
#check @norm_vertical_shift_le
#check @norm_height_shift_le
#check @norm_endpoint_shift_le
#check @norm_actual_perron_le
#check @norm_actual_perron_le_strong
#check @halfError
#check @closedError
#check @errorFunction
#check @truncationError_le_halfError
#check @actualError_le_closedError
#check @closedError_le_errorFunction
#check @norm_perron_le_errorFunction
#check @sourceError
#check @source_right_perron_function
#check @exp_small_le
#check @two_rpow_source_le
#check @rpow_small_source_le
#check @rpow_source_le
#check @series_factor_source_le
#check @halfError_source_le
#check @halfErrors_source_le
#check @heightError_source_le
#check @endpointFunction_source_le
#check @log_two_source_le
#check @sourceError_le
#check @source_right_perron_le
#check @primitiveError
#check @nonprincipalError
#check @primitive_psi_function
#check @primitiveError_le
#check @primitive_psi_le
#check @nonprincipal_psi_function
#check @nonprincipalError_le
#check @nonprincipal_psi_le
#check @oscillatoryError
#check @nonprincipal_oscillation_function
#check @oscillatoryError_le
#check @nonprincipal_oscillation_le
#check @primitive_nonprincipal_psi_sum
#check @nonprincipal_psi_sum
#check @nonprincipal_psi_sum_multiplicity
#check @nonprincipal_closed_window
#check @nonprincipal_twistedS

#print axioms seriesBound
#print axioms seriesBound_nonneg
#print axioms mangoldt_normSum_le
#print axioms normSum_twisted_le
#print axioms norm_logDeriv_le
#print axioms source_abscissa_mem
#print axioms seriesBound_source
#print axioms truncationError
#print axioms heightError
#print axioms endpointError
#print axioms actualError
#print axioms normSum_twisted_le_of_majorant
#print axioms norm_logDeriv_le_of_majorant
#print axioms norm_character_perron_le
#print axioms norm_vertical_shift_le
#print axioms norm_height_shift_le
#print axioms norm_endpoint_shift_le
#print axioms norm_actual_perron_le
#print axioms norm_actual_perron_le_strong
#print axioms halfError
#print axioms closedError
#print axioms errorFunction
#print axioms truncationError_le_halfError
#print axioms actualError_le_closedError
#print axioms closedError_le_errorFunction
#print axioms norm_perron_le_errorFunction
#print axioms sourceError
#print axioms source_right_perron_function
#print axioms exp_small_le
#print axioms two_rpow_source_le
#print axioms rpow_small_source_le
#print axioms rpow_source_le
#print axioms series_factor_source_le
#print axioms halfError_source_le
#print axioms halfErrors_source_le
#print axioms heightError_source_le
#print axioms endpointFunction_source_le
#print axioms log_two_source_le
#print axioms sourceError_le
#print axioms source_right_perron_le
#print axioms primitiveError
#print axioms nonprincipalError
#print axioms primitive_psi_function
#print axioms primitiveError_le
#print axioms primitive_psi_le
#print axioms nonprincipal_psi_function
#print axioms nonprincipalError_le
#print axioms nonprincipal_psi_le
#print axioms oscillatoryError
#print axioms nonprincipal_oscillation_function
#print axioms oscillatoryError_le
#print axioms nonprincipal_oscillation_le
#print axioms primitive_nonprincipal_psi_sum
#print axioms nonprincipal_psi_sum
#print axioms nonprincipal_psi_sum_multiplicity
#print axioms nonprincipal_closed_window
#print axioms nonprincipal_twistedS
