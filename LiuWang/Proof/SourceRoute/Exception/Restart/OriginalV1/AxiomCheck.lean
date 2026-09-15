import LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1.EulerSeries
import LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1.PrimeSupport
import LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1.WindowDomain
import LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1.InducedCharacter

set_option autoImplicit false
set_option pp.universes true
set_option pp.explicit true

namespace LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1

#check @kappa
#print axioms kappa
#check @kappa_eq
#print axioms kappa_eq
#check @f
#print axioms f
#check @f_eq_damped
#print axioms f_eq_damped
#check @s
#print axioms s
#check @badS
#print axioms badS
#check @s_eq
#print axioms s_eq
#check @badS_eq
#print axioms badS_eq
#check @badS_nonneg
#print axioms badS_nonneg
#check @abs_f_sub_primitive_le
#print axioms abs_f_sub_primitive_le
#check @abs_f_principal_sub_zeta_le
#print axioms abs_f_principal_sub_zeta_le
#check @principal_at_zero_identity
#print axioms principal_at_zero_identity
#check @NontrivialZeroIndex
#print axioms NontrivialZeroIndex
#check @zeroSum
#print axioms zeroSum
#check @primitiveIndexEquiv
#print axioms primitiveIndexEquiv
#check @zeroSum_eq_primitive
#print axioms zeroSum_eq_primitive
#check @completed_multiplicity
#print axioms completed_multiplicity
#check @completedIndexEquiv
#print axioms completedIndexEquiv
#check @zeroSum_eq_completed
#print axioms zeroSum_eq_completed
#check @zeroSum_summable
#print axioms zeroSum_summable
#check @parityShift
#print axioms parityShift
#check @gammaTerm
#print axioms gammaTerm
#check @gammaDifference_eq
#print axioms gammaDifference_eq
#check @l25_primitive_identity
#print axioms l25_primitive_identity
#check @l25_primitive_of_gamma_estimate
#print axioms l25_primitive_of_gamma_estimate
#check @l25_imprimitive_of_gamma_estimate
#print axioms l25_imprimitive_of_gamma_estimate
#check @principalEulerDifference
#print axioms principalEulerDifference
#check @l24_euler_identity
#print axioms l24_euler_identity
#check @principalEulerDifference_bound
#print axioms principalEulerDifference_bound
#check @l24_zeta_identity
#print axioms l24_zeta_identity
#check @l24_principal_identity
#print axioms l24_principal_identity
#check @poleDifference_le_reciprocal
#print axioms poleDifference_le_reciprocal
#check @l24_low_of_gamma_estimate
#print axioms l24_low_of_gamma_estimate
#check @l24_high_of_gamma_estimate
#print axioms l24_high_of_gamma_estimate
#check @s_nonneg
#print axioms s_nonneg
#check @badS_add_s
#print axioms badS_add_s
#check @badS_eq_sub
#print axioms badS_eq_sub
#check @badS_le_s
#print axioms badS_le_s
#check @primitive_badS_zero
#print axioms primitive_badS_zero
#check @nontrivialZeroIndex_zero
#print axioms nontrivialZeroIndex_zero
#check @parityShift_eq_complex
#print axioms parityShift_eq_complex
#check @windowValues
#print axioms windowValues
#check @mem_windowValues
#print axioms mem_windowValues
#check @windowValues_eq_primitive
#print axioms windowValues_eq_primitive
#check @window_sum_eq_primitive
#print axioms window_sum_eq_primitive
#check @windowCount
#print axioms windowCount
#check @windowCount_eq_primitive
#print axioms windowCount_eq_primitive
#check @windowCount_mono_height
#print axioms windowCount_mono_height
#check @originalCutoff
#print axioms originalCutoff
#check @original_window_sum_transport
#print axioms original_window_sum_transport
#check @original_window_count_le_conductor
#print axioms original_window_count_le_conductor
#check @excludedEulerTerm
#print axioms excludedEulerTerm
#check @excludedEulerTerm_eq
#print axioms excludedEulerTerm_eq
#check @complexEuler_hasSum
#print axioms complexEuler_hasSum
#check @excludedEulerTerm_hasSum
#print axioms excludedEulerTerm_hasSum
#check @excludedDampedTerm
#print axioms excludedDampedTerm
#check @excludedDampedTerm_hasSum
#print axioms excludedDampedTerm_hasSum
#check @principalEulerDifference_eq_series
#print axioms principalEulerDifference_eq_series
#check @l24_equation_25
#print axioms l24_equation_25
#check @excludedDampedSeries_norm_le
#print axioms excludedDampedSeries_norm_le
#check @originalCutoff_pos
#print axioms originalCutoff_pos
#check @mem_original_window
#print axioms mem_original_window
#check @parityShift_primitive
#print axioms parityShift_primitive
#check @parityShift_changeLevel
#print axioms parityShift_changeLevel
#check @induced_conductor
#print axioms induced_conductor
#check @l25_induced_of_gamma_estimate
#print axioms l25_induced_of_gamma_estimate

end LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1
